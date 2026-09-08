#!/usr/bin/env python3
"""Classify a bounded bare-metal serial capture against a named manifest.

Operator procedure and evidence-bundle requirements are documented in
``docs/bare-metal-rejection-capture.md``.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

MAX_CAPTURE_BYTES = 1024 * 1024
MAX_MANIFEST_BYTES = 64 * 1024
MAX_PROTOCOL_BYTES = 1024 * 1024
MAX_MACHINE_FIELD_CHARS = 512
HEX64 = re.compile(r"^[0-9a-f]{64}$")
HEX40 = re.compile(r"^[0-9a-f]{40}$")
FORBIDDEN = re.compile(
    r"^LEANOS/[0-9]+ (CPL3|ENTER|ENTRY|TIMER|CONTEXT|SWITCH|SYSCALL|PEER|TLB-CPL3|FINAL)(?:\s|$)"
)
MACHINE_FIELDS = ("model", "cpu", "firmware", "uart", "captureAdapter")
RECORD_IDENTITY = re.compile(r"^(LEANOS/[0-9]+ [A-Z0-9_-]+)(?:\s|$)")
PRETERMINAL_AUTHORITY = re.compile(
    r"(?:^|\s)(?:origin=cpl3|cpl=3|(?:status|result)=(?:PASS|FAIL))(?:\s|$)"
)
PROTOCOL_PREFIX = "LEANOS" + "/"
# These are the only production record families emitted as ordinary
# platform-admission failures before CPL3. Generated-protocol membership alone
# is insufficient: another real record identity must not be relabeled FAIL.
REJECTION_TERMINAL_IDENTITIES = frozenset(
    (f"{PROTOCOL_PREFIX}3 FINAL", f"{PROTOCOL_PREFIX}7 BOOTALLOC")
)


class ClassificationError(Exception):
    def __init__(self, result: str, detail: str):
        super().__init__(detail)
        self.result = result
        self.detail = detail


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_bounded(path: Path, limit: int, result: str, detail: str) -> bytes:
    with path.open("rb") as stream:
        value = stream.read(limit + 1)
    if len(value) > limit:
        raise ClassificationError(result, detail)
    return value


def load_manifest(path: Path) -> dict:
    raw = read_bounded(
        path, MAX_MANIFEST_BYTES, "manifest-invalid", "manifest exceeds byte bound"
    )
    try:
        value = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ClassificationError(
            "manifest-invalid", "manifest is not valid UTF-8 JSON"
        ) from error
    if not isinstance(value, dict) or set(value) != {
        "schemaVersion", "sourceRevision", "isoSha256", "elfSha256",
        "serialProtocolSha256",
        "expectedPrefix", "expectedTerminal", "machine",
    } or type(value["schemaVersion"]) is not int or value["schemaVersion"] != 1:
        raise ClassificationError("manifest-invalid", "unsupported manifest shape")
    if not isinstance(value["sourceRevision"], str) or not HEX40.fullmatch(
        value["sourceRevision"]
    ):
        raise ClassificationError("manifest-invalid", "invalid source revision")
    if not all(
        isinstance(value[field], str) and HEX64.fullmatch(value[field])
        for field in ("isoSha256", "elfSha256", "serialProtocolSha256")
    ):
        raise ClassificationError("manifest-invalid", "invalid artifact digest")
    prefix = value["expectedPrefix"]
    if (not isinstance(prefix, list) or len(prefix) > 256
            or not all(isinstance(line, str) and 0 < len(line) <= 512
                       and re.fullmatch(r"LEANOS/[0-9]+ [A-Z0-9_-]+(?: .*)?", line)
                       and " status=FAIL " not in line for line in prefix)):
        raise ClassificationError("manifest-invalid", "invalid expected prefix")
    terminal = value["expectedTerminal"]
    if not isinstance(terminal, str) or not re.fullmatch(
        r"LEANOS/[0-9]+ [A-Z0-9_-]+ status=FAIL reason=[a-z0-9-]+", terminal
    ):
        raise ClassificationError("manifest-invalid", "invalid expected terminal")
    machine = value["machine"]
    if not isinstance(machine, dict) or set(machine) != set(MACHINE_FIELDS) or not all(
        isinstance(machine[field], str)
        and machine[field].strip()
        and len(machine[field]) <= MAX_MACHINE_FIELD_CHARS
        for field in MACHINE_FIELDS
    ):
        raise ClassificationError("manifest-invalid", "incomplete machine identity")
    return value


def load_protocol(path: Path, source_revision: str) -> frozenset[str]:
    try:
        lines = read_bounded(
            path, MAX_PROTOCOL_BYTES, "manifest-invalid",
            "serial protocol exceeds byte bound",
        ).decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        raise ClassificationError(
            "manifest-invalid", "serial protocol is not UTF-8"
        ) from error
    if lines[:2] != [
        "leanos-serial-protocol\t1",
        f"source-revision\t{source_revision}",
    ]:
        raise ClassificationError(
            "manifest-invalid", "serial protocol header or source revision differs"
        )
    identities = set()
    symbols = set()
    for line in lines[2:]:
        fields = line.split("\t")
        if fields[0] == "family" and len(fields) == 4:
            version, symbol, identity = fields[1:]
            valid = (
                version.isdigit()
                and symbol == f"LEANOS_SERIAL_FAMILY_{version}"
                and identity == f"LEANOS/{version}"
            )
        elif fields[0] == "record" and len(fields) == 5:
            version, tag, symbol, identity = fields[1:]
            valid = (
                version.isdigit()
                and re.fullmatch(r"[A-Z][A-Z0-9-]*", tag) is not None
                and symbol == f"LEANOS_SERIAL_{version}_{tag.replace('-', '_')}"
                and identity == f"LEANOS/{version} {tag}"
            )
            if valid:
                if identity in identities:
                    valid = False
                identities.add(identity)
        else:
            valid = False
            symbol = ""
        if not valid or symbol in symbols:
            raise ClassificationError(
                "manifest-invalid", "malformed or duplicate serial protocol row"
            )
        symbols.add(symbol)
    if not identities:
        raise ClassificationError("manifest-invalid", "serial protocol is empty")
    return frozenset(identities)


def require_protocol_record(line: str, identities: frozenset[str]) -> None:
    match = RECORD_IDENTITY.match(line)
    if match is None or match.group(1) not in identities:
        raise ClassificationError(
            "manifest-invalid", "manifest record is outside generated protocol"
        )


def is_platform_rejection(line: str) -> bool:
    identity = RECORD_IDENTITY.match(line)
    return (
        identity is not None
        and identity.group(1) in REJECTION_TERMINAL_IDENTITIES
        and re.fullmatch(
            r"LEANOS/[0-9]+ [A-Z0-9_-]+ status=FAIL reason=[a-z0-9-]+", line
        ) is not None
    )


def classify(manifest_path: Path, iso: Path, elf: Path, capture: Path,
             source_revision: str, serial_protocol: Path | None = None) -> dict:
    manifest = load_manifest(manifest_path)
    protocol_path = serial_protocol or Path(os.environ.get(
        "LEANOS_SERIAL_PROTOCOL_TSV", "build/boot/serial-protocol.tsv"
    ))
    if source_revision != manifest["sourceRevision"]:
        raise ClassificationError("digest-mismatch", "source revision mismatch")
    if sha256(protocol_path) != manifest["serialProtocolSha256"]:
        raise ClassificationError("digest-mismatch", "serial protocol digest mismatch")
    protocol = load_protocol(protocol_path, manifest["sourceRevision"])
    for line in manifest["expectedPrefix"]:
        require_protocol_record(line, protocol)
        if PRETERMINAL_AUTHORITY.search(line):
            raise ClassificationError(
                "manifest-invalid", "pre-terminal authority record is forbidden"
            )
    require_protocol_record(manifest["expectedTerminal"], protocol)
    terminal_identity = RECORD_IDENTITY.match(manifest["expectedTerminal"])
    if (
        terminal_identity is None
        or terminal_identity.group(1) not in REJECTION_TERMINAL_IDENTITIES
    ):
        raise ClassificationError(
            "manifest-invalid", "terminal identity is not a platform rejection"
        )
    if sha256(iso) != manifest["isoSha256"] or sha256(elf) != manifest["elfSha256"]:
        raise ClassificationError("digest-mismatch", "artifact digest mismatch")
    data = read_bounded(
        capture,
        MAX_CAPTURE_BYTES,
        "capture-failure",
        "capture exceeds byte bound",
    )
    if not data:
        raise ClassificationError("silence-timeout", "capture is empty")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ClassificationError("malformed-protocol", "capture is not UTF-8") from error
    lines = text.replace("\r\n", "\n").replace("\r", "\n").splitlines()
    expected = manifest["expectedTerminal"]
    terminal_indexes = [index for index, line in enumerate(lines) if " status=FAIL reason=" in line]
    if any(
        FORBIDDEN.match(line)
        and not (
            index == len(lines) - 1
            and (line == expected or is_platform_rejection(line))
        )
        for index, line in enumerate(lines)
    ):
        raise ClassificationError("unexpected-success", "runtime authority record observed")
    if expected not in lines:
        result = "wrong-rejection" if terminal_indexes else "malformed-protocol"
        raise ClassificationError(result, "exact expected terminal not observed")
    if lines.count(expected) != 1:
        raise ClassificationError("malformed-protocol", "terminal record is duplicated")
    if lines[-1] != expected:
        raise ClassificationError("post-terminal-output", "output follows terminal record")
    if lines != manifest["expectedPrefix"] + [expected]:
        raise ClassificationError(
            "malformed-protocol", "pre-terminal protocol differs from manifest"
        )
    return {
        "schemaVersion": 1,
        "result": "exact-typed-rejection",
        "sourceRevision": source_revision,
        "isoSha256": manifest["isoSha256"],
        "elfSha256": manifest["elfSha256"],
        "serialProtocolSha256": manifest["serialProtocolSha256"],
        "captureSha256": hashlib.sha256(data).hexdigest(),
        "captureBytes": len(data),
        "machine": manifest["machine"],
        "expectedTerminal": expected,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("iso", type=Path)
    parser.add_argument("elf", type=Path)
    parser.add_argument("capture", type=Path)
    parser.add_argument("--serial-protocol", type=Path)
    parser.add_argument("--source-revision", required=True)
    args = parser.parse_args()
    try:
        result = classify(args.manifest, args.iso, args.elf, args.capture,
                          args.source_revision, args.serial_protocol)
    except ClassificationError as error:
        print(json.dumps({"schemaVersion": 1, "result": error.result,
                          "detail": error.detail}, sort_keys=True))
        return 1
    except (OSError, ValueError, TypeError, json.JSONDecodeError):
        print(json.dumps({"schemaVersion": 1, "result": "capture-failure",
                          "detail": "input is unreadable or invalid"}, sort_keys=True))
        return 1
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
