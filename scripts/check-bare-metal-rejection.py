#!/usr/bin/env python3
"""Classify a bounded bare-metal serial capture against a named manifest."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

MAX_CAPTURE_BYTES = 1024 * 1024
HEX64 = re.compile(r"^[0-9a-f]{64}$")
HEX40 = re.compile(r"^[0-9a-f]{40}$")
FORBIDDEN = re.compile(
    r"^LEANOS/[0-9]+ (CPL3|ENTER|ENTRY|TIMER|CONTEXT|SWITCH|SYSCALL|PEER|TLB-CPL3|FINAL)(?:\s|$)"
)
MACHINE_FIELDS = ("model", "cpu", "firmware", "uart", "captureAdapter")


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


def load_manifest(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if set(value) != {
        "schemaVersion", "sourceRevision", "isoSha256", "elfSha256",
        "expectedPrefix", "expectedTerminal", "machine",
    } or value["schemaVersion"] != 1:
        raise ClassificationError("manifest-invalid", "unsupported manifest shape")
    if not HEX40.fullmatch(value["sourceRevision"]):
        raise ClassificationError("manifest-invalid", "invalid source revision")
    if not all(HEX64.fullmatch(value[field]) for field in ("isoSha256", "elfSha256")):
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
    if set(machine) != set(MACHINE_FIELDS) or not all(
        isinstance(machine[field], str) and machine[field].strip()
        for field in MACHINE_FIELDS
    ):
        raise ClassificationError("manifest-invalid", "incomplete machine identity")
    return value


def classify(manifest_path: Path, iso: Path, elf: Path, capture: Path,
             source_revision: str) -> dict:
    manifest = load_manifest(manifest_path)
    if source_revision != manifest["sourceRevision"]:
        raise ClassificationError("digest-mismatch", "source revision mismatch")
    if sha256(iso) != manifest["isoSha256"] or sha256(elf) != manifest["elfSha256"]:
        raise ClassificationError("digest-mismatch", "artifact digest mismatch")
    data = capture.read_bytes()
    if len(data) > MAX_CAPTURE_BYTES:
        raise ClassificationError("capture-failure", "capture exceeds byte bound")
    if not data:
        raise ClassificationError("silence-timeout", "capture is empty")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ClassificationError("malformed-protocol", "capture is not UTF-8") from error
    lines = text.replace("\r\n", "\n").replace("\r", "\n").splitlines()
    expected = manifest["expectedTerminal"]
    terminal_indexes = [index for index, line in enumerate(lines) if " status=FAIL reason=" in line]
    if any(FORBIDDEN.match(line) for line in lines):
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
    parser.add_argument("--source-revision", required=True)
    args = parser.parse_args()
    try:
        result = classify(args.manifest, args.iso, args.elf, args.capture,
                          args.source_revision)
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
