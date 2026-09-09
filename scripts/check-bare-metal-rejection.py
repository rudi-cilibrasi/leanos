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
import shutil
import sys
import tempfile

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
    r"(?:^|\s)(?:origin=cpl3|cpl=3|status=(?:PASS|FAIL)|result=FAIL)(?:\s|$)"
)
PRETERMINAL_PASS = re.compile(r"(?:^|\s)result=PASS(?:\s|$)")
PROTOCOL_PREFIX = "LEANOS" + "/"
# These are the only production record families emitted as ordinary
# platform-admission failures before CPL3. Generated-protocol membership alone
# is insufficient: another real record identity must not be relabeled FAIL.
REJECTION_TERMINAL_IDENTITIES = frozenset(
    (f"{PROTOCOL_PREFIX}3 FINAL", f"{PROTOCOL_PREFIX}7 BOOTALLOC")
)
PRE_ADMISSION_STATIC_IDENTITIES = frozenset((f"{PROTOCOL_PREFIX}1 SERIAL",))
BUNDLE_FILES = (
    "classification.json",
    "image.iso",
    "kernel.elf",
    "machine.json",
    "serial-protocol.tsv",
    "serial.normalized.log",
    "serial.raw.log",
    "source-revision.txt",
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


def load_protocol(
    path: Path, source_revision: str
) -> tuple[
    frozenset[str], frozenset[str], frozenset[str], frozenset[str], tuple[str, ...]
]:
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
    pre_admission_reasons = set()
    pre_admission_bootalloc_reasons = set()
    pre_admission_boot_records = set()
    pre_admission_phase_records = []
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
        elif fields[0] == "pre-admission-reason" and len(fields) == 2:
            reason = fields[1]
            valid = (
                re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", reason) is not None
                and reason not in pre_admission_reasons
            )
            pre_admission_reasons.add(reason)
            symbol = ""
        elif fields[0] == "pre-admission-bootalloc-reason" and len(fields) == 2:
            reason = fields[1]
            valid = (
                re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", reason) is not None
                and reason not in pre_admission_bootalloc_reasons
            )
            pre_admission_bootalloc_reasons.add(reason)
            symbol = ""
        elif fields[0] == "pre-admission-boot-record" and len(fields) == 3:
            version, tag = fields[1:]
            identity = f"LEANOS/{version} {tag}"
            valid = (
                version.isdigit()
                and tag == "BOOT"
                and identity in identities
                and identity not in pre_admission_boot_records
            )
            pre_admission_boot_records.add(identity)
            symbol = ""
        elif fields[0] == "pre-admission-record" and len(fields) == 3:
            version, tag = fields[1:]
            identity = f"LEANOS/{version} {tag}"
            valid = (
                version.isdigit()
                and re.fullmatch(r"[A-Z][A-Z0-9-]*", tag) is not None
                and identity in identities
                and identity not in pre_admission_phase_records
            )
            pre_admission_phase_records.append(identity)
            symbol = ""
        else:
            valid = False
            symbol = ""
        if not valid or symbol in symbols:
            raise ClassificationError(
                "manifest-invalid", "malformed or duplicate serial protocol row"
            )
        if symbol:
            symbols.add(symbol)
    if (
        not identities
        or not pre_admission_reasons
        or not pre_admission_bootalloc_reasons
        or not pre_admission_boot_records
        or not pre_admission_phase_records
    ):
        raise ClassificationError("manifest-invalid", "serial protocol is empty")
    return (
        frozenset(identities),
        frozenset(pre_admission_reasons),
        frozenset(pre_admission_bootalloc_reasons),
        frozenset(pre_admission_boot_records),
        tuple(pre_admission_phase_records),
    )


def require_protocol_record(line: str, identities: frozenset[str]) -> None:
    match = RECORD_IDENTITY.match(line)
    if match is None or match.group(1) not in identities:
        raise ClassificationError(
            "manifest-invalid", "manifest record is outside generated protocol"
        )


def require_pre_admission_order(
    lines: list[str],
    boot_records: frozenset[str],
    phase_records: tuple[str, ...],
    terminal_identity: str,
) -> None:
    """Require the generated pre-admission phases in their emitter order.

    SERIAL and the scenario BOOT record are singleton phase boundaries. Later
    generated phase identities may repeat (for example DMA-FUNCTION per PCI
    function), but may not move backwards in the Lean-owned row order.
    """
    phase_order = {identity: index for index, identity in enumerate(phase_records)}
    seen_serial = False
    seen_boot = False
    seen_phases = set()
    last_phase = -1
    for line in lines:
        match = RECORD_IDENTITY.match(line)
        if match is None:
            raise ClassificationError("manifest-invalid", "invalid pre-admission record")
        identity = match.group(1)
        if identity in PRE_ADMISSION_STATIC_IDENTITIES:
            if seen_serial or seen_boot or last_phase >= 0:
                raise ClassificationError(
                    "manifest-invalid", "pre-admission static record is reordered"
                )
            seen_serial = True
        elif identity in boot_records:
            if seen_boot or last_phase >= 0:
                raise ClassificationError(
                    "manifest-invalid", "pre-admission boot record is reordered or duplicated"
                )
            seen_boot = True
        else:
            rank = phase_order.get(identity)
            if rank is None or rank < last_phase:
                raise ClassificationError(
                    "manifest-invalid", "pre-admission phase record is reordered"
                )
            last_phase = rank
            seen_phases.add(identity)
    if not seen_serial or not seen_boot:
        raise ClassificationError(
            "manifest-invalid", "pre-admission boundaries are incomplete"
        )
    required_phases = set(phase_records)
    if terminal_identity == f"{PROTOCOL_PREFIX}7 BOOTALLOC" and seen_phases != required_phases:
        raise ClassificationError(
            "manifest-invalid", "boot-allocation rejection phases are incomplete"
        )
    if terminal_identity == f"{PROTOCOL_PREFIX}3 FINAL" and seen_phases:
        raise ClassificationError(
            "manifest-invalid", "pre-admission final includes post-quarantine phases"
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
    (protocol, pre_admission_reasons, pre_admission_bootalloc_reasons,
     pre_admission_boot_records,
     pre_admission_phase_records) = load_protocol(
        protocol_path, manifest["sourceRevision"]
    )
    for line in manifest["expectedPrefix"]:
        require_protocol_record(line, protocol)
        identity = RECORD_IDENTITY.match(line)
        if identity is None or identity.group(1) not in (
            PRE_ADMISSION_STATIC_IDENTITIES
            | pre_admission_boot_records
            | frozenset(pre_admission_phase_records)
        ):
            raise ClassificationError(
                "manifest-invalid",
                "pre-terminal record is outside the generated pre-admission phase",
            )
        if PRETERMINAL_AUTHORITY.search(line) or (
            PRETERMINAL_PASS.search(line)
            and identity.group(1) not in pre_admission_phase_records
        ):
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
    require_pre_admission_order(
        manifest["expectedPrefix"],
        pre_admission_boot_records,
        pre_admission_phase_records,
        terminal_identity.group(1),
    )
    terminal_reason = manifest["expectedTerminal"].rsplit("reason=", 1)[1]
    if (
        terminal_identity.group(1) == f"{PROTOCOL_PREFIX}3 FINAL"
        and terminal_reason not in pre_admission_reasons
    ):
        raise ClassificationError(
            "manifest-invalid", "terminal reason is not a pre-admission rejection"
        )
    if (
        terminal_identity.group(1) == f"{PROTOCOL_PREFIX}7 BOOTALLOC"
        and terminal_reason not in pre_admission_bootalloc_reasons
    ):
        raise ClassificationError(
            "manifest-invalid", "terminal reason is not a boot-allocation rejection"
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
    normalized_text = text.replace("\r\n", "\n").replace("\r", "\n")
    normalized = normalized_text.encode("utf-8")
    lines = normalized_text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
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
        "normalizedCaptureSha256": hashlib.sha256(normalized).hexdigest(),
        "normalizedCaptureBytes": len(normalized),
        "captureLines": len(lines),
        "machine": manifest["machine"],
        "expectedTerminal": expected,
    }


def emit_evidence_bundle(
    directory: Path,
    result: dict,
    manifest: Path,
    iso: Path,
    elf: Path,
    capture: Path,
    serial_protocol: Path,
) -> None:
    """Atomically emit the deterministic, content-addressed bundle core."""
    if directory.exists():
        raise ClassificationError("capture-failure", "bundle output already exists")
    directory.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{directory.name}.", dir=directory.parent))
    try:
        shutil.copyfile(manifest, temporary / "machine.json")
        shutil.copyfile(iso, temporary / "image.iso")
        shutil.copyfile(elf, temporary / "kernel.elf")
        shutil.copyfile(capture, temporary / "serial.raw.log")
        shutil.copyfile(serial_protocol, temporary / "serial-protocol.tsv")
        raw_capture = (temporary / "serial.raw.log").read_bytes()
        normalized = raw_capture.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
        (temporary / "serial.normalized.log").write_text(normalized, encoding="utf-8")
        (temporary / "source-revision.txt").write_text(
            result["sourceRevision"] + "\n", encoding="ascii"
        )
        (temporary / "classification.json").write_text(
            json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
        digest_lines = [
            f"{sha256(temporary / name)}  {name}" for name in BUNDLE_FILES
        ]
        (temporary / "SHA256SUMS").write_text(
            "\n".join(digest_lines) + "\n", encoding="ascii"
        )
        temporary.rename(directory)
    except Exception:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def verify_evidence_bundle(directory: Path, *, include_observation: bool = False) -> dict:
    """Verify the exact bundle inventory and re-run classification from it."""
    retained_names = list(BUNDLE_FILES)
    if include_observation:
        retained_names.append("observation.json")
    retained_names.sort()
    expected_names = set(retained_names) | {"SHA256SUMS"}
    if not directory.is_dir():
        raise ClassificationError("manifest-invalid", "bundle file inventory differs")
    entries = tuple(directory.iterdir())
    if (
        {entry.name for entry in entries} != expected_names
        or any(entry.is_symlink() or not entry.is_file() for entry in entries)
    ):
        raise ClassificationError("manifest-invalid", "bundle file inventory differs")
    lines = (directory / "SHA256SUMS").read_text(encoding="ascii").splitlines()
    expected_lines = [f"{sha256(directory / name)}  {name}" for name in retained_names]
    if lines != expected_lines:
        raise ClassificationError("digest-mismatch", "bundle digest inventory differs")
    manifest = load_manifest(directory / "machine.json")
    revision_text = (directory / "source-revision.txt").read_text(encoding="ascii")
    if revision_text != manifest["sourceRevision"] + "\n":
        raise ClassificationError("digest-mismatch", "bundle source revision differs")
    observed = classify(
        directory / "machine.json",
        directory / "image.iso",
        directory / "kernel.elf",
        directory / "serial.raw.log",
        manifest["sourceRevision"],
        directory / "serial-protocol.tsv",
    )
    retained = json.loads((directory / "classification.json").read_text(encoding="utf-8"))
    if retained != observed:
        raise ClassificationError("digest-mismatch", "retained classification differs")
    normalized = (directory / "serial.normalized.log").read_bytes()
    if (
        hashlib.sha256(normalized).hexdigest() != observed["normalizedCaptureSha256"]
        or len(normalized) != observed["normalizedCaptureBytes"]
    ):
        raise ClassificationError("digest-mismatch", "normalized capture differs")
    return observed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("iso", type=Path)
    parser.add_argument("elf", type=Path)
    parser.add_argument("capture", type=Path)
    parser.add_argument("--serial-protocol", type=Path)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--bundle-dir", type=Path)
    args = parser.parse_args()
    try:
        result = classify(args.manifest, args.iso, args.elf, args.capture,
                          args.source_revision, args.serial_protocol)
        if args.bundle_dir is not None:
            emit_evidence_bundle(
                args.bundle_dir,
                result,
                args.manifest,
                args.iso,
                args.elf,
                args.capture,
                args.serial_protocol or Path(os.environ.get(
                    "LEANOS_SERIAL_PROTOCOL_TSV", "build/boot/serial-protocol.tsv"
                )),
            )
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
