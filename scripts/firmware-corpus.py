#!/usr/bin/env python3
"""Firmware handoff corpus: validate the corpus manifest, convert each
capture into the exact bytes the boot decoders consume, derive controlled
mutations, and emit the replay driver and Lean checks that hold the generated C
and the Lean definitions to the manifest's expectations.

The corpus (firmware-corpus/) holds raw captures produced by
scripts/capture-firmware-handoff.sh on real machines and firmware: the
firmware-provided E820 map, the raw MADT, and the executing processor's APIC
identity. This tool wraps the E820 entries into a Multiboot2 information
structure exactly as captured (same order, no merging, no repair) and passes
the MADT through byte for byte; docs/firmware-handoff-corpus.md states the
conversion contract. Every case declares its expected decode/admission words,
so a decoder change that alters a real-firmware result fails here first.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
import sys
import firmware_root_corpus as roots
import native_handoff_corpus as native
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "firmware-corpus"
MANIFEST = CORPUS / "manifest.json"
SCHEMA = "leanos-firmware-corpus-v1"

MULTIBOOT2_MAGIC = 0x36D76289
# The information structure's physical address is not a captured value; the
# decoder only requires it 8-byte aligned and at or above one page.
INFO_ADDRESS = 0x1000
MEMORY_MAP_TAG = 6
END_TAG = 0
ENTRY_SIZE = 24
ENTRY_VERSION = 0
MAX_TAG_BYTES = 65536

# Linux's names for the firmware-provided E820 entry types, as printed by
# /sys/firmware/memmap (arch/x86/kernel/e820.c), and the E820 type numbers
# they stand for. Multiboot2 defines types 1 to 5 with the same numbering, and
# the decoder classifies every other value as reserved without repairing it.
E820_TYPES = {
    "System RAM": 1,
    "Reserved": 2,
    "ACPI Tables": 3,
    "ACPI Non-volatile Storage": 4,
    "Unusable memory": 5,
    "Persistent Memory": 7,
    "Persistent Memory (legacy)": 12,
    "Soft Reserved": 0xEFFFFFFF,
}

# Stable result codes mirrored from LeanOS/BootMemoryMapDecoderABI.lean and
# LeanOS/BootTopology.lean. Both evaluators check the manifest words, so a
# mirror that drifts from the model fails the corpus gate.
DECODER_ERRORS = {
    "badMagic": 1, "unalignedInfo": 2, "bufferTooSmall": 3, "bufferTooLarge": 4,
    "truncatedField": 5, "advertisedSizeMismatch": 6, "nonzeroInfoReserved": 7,
    "tooManyTags": 8, "malformedTagSize": 9, "tagOutOfBounds": 10,
    "missingEndTag": 12, "misplacedEndTag": 13, "missingMemoryMap": 14,
    "duplicateMemoryMap": 15, "badEntrySize": 16, "unsupportedEntryVersion": 17,
    "tooManyEntries": 18, "nonzeroEntryReserved": 19, "zeroLengthEntry": 20,
    "entryAddressOverflow": 21, "typedHandoffRejected": 22, "internalBounds": 23,
    "infoAddressBelowMinimum": 24,
}
NORMALIZER_ERRORS = {
    "badMagic": 1, "unalignedInfo": 2, "malformedInfoSize": 3, "tooManyTags": 4,
    "tagBytesExceeded": 5, "malformedTagSize": 6, "missingEndTag": 7,
    "misplacedEndTag": 8, "missingMemoryMap": 9, "duplicateMemoryMap": 10,
    "badEntrySize": 11, "unsupportedEntryVersion": 12, "tooManyEntries": 13,
    "zeroLength": 14, "addressOverflow": 15, "expandedFramesExceeded": 16,
    "normalizedRegionsExceeded": 17, "normalizationInvariant": 18,
    "allocatorRejected": 19,
}
MADT_DECODER_ERRORS = {
    "truncatedHeader": 1, "truncatedRecord": 2, "invalidRecordLength": 3,
    "unsupportedRecordKind": 4, "processorOverflow": 5, "truncatedMadtHeader": 6,
    "sdtTruncatedHeader": 7, "sdtInvalidSignature": 8, "sdtInvalidLength": 9,
    "sdtTableTooLarge": 10, "sdtInvalidChecksum": 11,
}
ADMISSION_ERRORS = {
    "unsupportedSource": 1, "unsupportedVersion": 2, "tooManyProcessors": 3,
    "duplicateApicId": 4, "onlineCapableProcessor": 5, "noEnabledProcessor": 6,
    "multipleEnabledProcessors": 7, "bspMismatch": 8,
}
STATUS_ACCEPTED, STATUS_DECODER, STATUS_POLICY = 1, 2, 3
HANDOFF_RESULT_TABLES = {"decoder-rejected": DECODER_ERRORS, "normalizer-rejected": NORMALIZER_ERRORS}
MADT_RESULT_TABLES = {"decoder-rejected": MADT_DECODER_ERRORS, "admission-rejected": ADMISSION_ERRORS}

CASE_ID = re.compile(r"^[a-z0-9][a-z0-9-]{2,63}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")


class CorpusError(Exception):
    pass


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CorpusError(message)


# --- manifest -------------------------------------------------------------

def load_manifest(path: Path = MANIFEST) -> dict:
    global CORPUS
    CORPUS = path.resolve().parent
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CorpusError(f"cannot read corpus manifest {path}: {error}") from error
    require(isinstance(manifest, dict) and manifest.get("schema") == SCHEMA,
            f"corpus manifest must declare schema {SCHEMA}")
    cases = manifest.get("cases")
    require(isinstance(cases, list) and cases, "corpus manifest must list at least one case")
    return manifest


def check_result(stage: str, result: str, words: list, tables: dict) -> None:
    """The named result and the pinned words must agree, and the reason must
    come from the model's closed vocabulary."""
    require(isinstance(words, list) and len(words) >= 3 and
            all(isinstance(word, int) and 0 <= word < 2**64 for word in words),
            f"{stage}: words must be a list of at least three 64-bit values")
    require(words[0] == 1, f"{stage}: word 0 must be ABI version 1")
    if result == "accepted":
        require(words[1] == STATUS_ACCEPTED, f"{stage}: accepted result needs status 1")
        return
    kind, _, reason = result.partition(":")
    require(kind in tables and reason in tables[kind],
            f"{stage}: unknown result {result!r}; reasons must be model-owned names")
    status = STATUS_DECODER if kind == "decoder-rejected" else STATUS_POLICY
    require(words[1] == status and words[2] == tables[kind][reason],
            f"{stage}: result {result!r} disagrees with words {words[:3]}")
    require(all(word == 0 for word in words[3:]), f"{stage}: rejected words carry only status and reason")


def validate_case(case: dict, seen_ids: set) -> None:
    require(isinstance(case, dict), "each case must be an object")
    case_id = case.get("id")
    require(isinstance(case_id, str) and CASE_ID.match(case_id), f"malformed case id {case_id!r}")
    require(case_id not in seen_ids, f"duplicate case id {case_id}")
    seen_ids.add(case_id)
    prefix = f"case {case_id}"
    for field in ("profile", "capture", "provenance", "permission", "redaction"):
        require(isinstance(case.get(field), str) and case[field].strip(), f"{prefix}: missing {field}")
    directory = CORPUS / case_id
    require(directory.is_dir(), f"{prefix}: directory {directory} is missing")
    inputs = case.get("inputs")
    require(case.get("root_tables") in ("unavailable", "acpidump", "freebsd-physical"),
            f"{prefix}: root_tables must be unavailable, acpidump or freebsd-physical")
    rooted = case["root_tables"] in ("acpidump", "freebsd-physical")
    expected_files = roots.capture_files(directory) if rooted else {
        "memmap.tsv", "acpi/APIC.bin", "executing-apic-id.txt", "provenance.json"}
    require(isinstance(inputs, dict) and set(inputs) == expected_files,
            f"{prefix}: inputs must name exactly the supported capture files")
    for name, digest in inputs.items():
        path = directory / name
        require(path.is_file(), f"{prefix}: input {name} is missing")
        require(isinstance(digest, str) and SHA256.match(digest), f"{prefix}: input {name} needs a sha256")
        require(sha256_file(path) == digest, f"{prefix}: input {name} does not match its recorded sha256")
    provenance = json.loads((directory / "provenance.json").read_text(encoding="utf-8"))
    require(provenance.get("root_tables") == case["root_tables"],
            f"{prefix}: root provenance disagrees with the manifest")
    for name in set(inputs) - {"provenance.json"}:
        require(provenance.get("files", {}).get(name) == inputs[name],
                f"{prefix}: capture provenance records a different {name}")
    if rooted:
        require((directory / "acpi/addresses.json").exists() == (case["root_tables"] == "freebsd-physical"),
                f"{prefix}: root address format disagrees with capture source")
    if case["root_tables"] == "freebsd-physical":
        roots.validate_freebsd_projection(directory)
    if rooted:
        def root_entry(entry, name):
            require(isinstance(entry, dict) and set(entry) == {"result", "words", "normalized_sha256"},
                    f"{prefix}: {name} needs result, words and normalized_sha256")
            words = entry["words"]
            require(isinstance(words, list) and len(words) == 5 and all(
                type(w) is int and 0 <= w < 2**64 for w in words), f"{prefix}: invalid root words")
            if words[1] == STATUS_DECODER:
                require(entry["result"] == roots.rejection_name(words), f"{prefix}: root result disagrees with words")
            else:
                check_result(f"{prefix} {name}", entry["result"], words, MADT_RESULT_TABLES)
            require(isinstance(entry["normalized_sha256"], str) and SHA256.fullmatch(entry["normalized_sha256"]),
                    f"{prefix}: malformed root digest")
        root_entry(case.get("root_replay"), "root_replay")
        root = roots.from_capture(directory, multiboot2_information(read_memmap(directory / "memmap.tsv")))
        mutations = case.get("root_mutations")
        require(isinstance(mutations, dict) and set(mutations) == set(roots.mutations(root)),
                f"{prefix}: root_mutations must pin every derived root mutation")
        for name, entry in mutations.items():
            root_entry(entry, name)
            require(entry["result"] != "accepted", f"{prefix}: root mutation {name} was accepted")
    else:
        require("root_replay" not in case and "root_mutations" not in case,
                f"{prefix}: unavailable roots cannot declare a replay")
    ids = case.get("apic")
    require(isinstance(ids, dict) and set(ids) == {"bsp", "executing"} and
            all(isinstance(ids[k], int) and 0 <= ids[k] <= 0xFFFFFFFF for k in ids),
            f"{prefix}: apic must give integer bsp and executing identities")
    executing = int((directory / "executing-apic-id.txt").read_text().strip())
    require(ids["executing"] == executing, f"{prefix}: apic.executing differs from the capture")
    expected = case.get("expected")
    require(isinstance(expected, dict) and set(expected) == {"handoff", "madt"},
            f"{prefix}: expected must have handoff and madt stages")
    for stage, tables in (("handoff", HANDOFF_RESULT_TABLES), ("madt", MADT_RESULT_TABLES)):
        entry = expected[stage]
        require(isinstance(entry, dict) and set(entry) == {"result", "words", "normalized_sha256"},
                f"{prefix}: expected.{stage} needs result, words, normalized_sha256")
        check_result(f"{prefix} {stage}", entry["result"], entry["words"], tables)
        require(isinstance(entry["normalized_sha256"], str) and SHA256.match(entry["normalized_sha256"]),
                f"{prefix}: expected.{stage}.normalized_sha256 must be a sha256")
    variants = case.get("handoff_variants")
    require(isinstance(variants, dict) and set(variants) == {"handoff-order-reversed", "handoff-overlapping-entry"},
            f"{prefix}: handoff_variants must pin both derived memory variants")
    for name, entry in variants.items():
        require(isinstance(entry, dict) and set(entry) == {"result", "words", "normalized_sha256"},
                f"{prefix}: {name} needs result, words and normalized_sha256")
        check_result(f"{prefix} {name}", entry["result"], entry["words"], HANDOFF_RESULT_TABLES)
        require(isinstance(entry["normalized_sha256"], str) and SHA256.fullmatch(entry["normalized_sha256"]),
                f"{prefix}: invalid memory variant digest")
    mutations = case.get("mutations")
    require(isinstance(mutations, dict) and set(mutations) == set(MUTATIONS),
            f"{prefix}: mutations must pin a result for each of {sorted(MUTATIONS)}")
    for name, result in mutations.items():
        stage, tables = ("madt", MADT_RESULT_TABLES) if name.startswith("madt-") else ("handoff", HANDOFF_RESULT_TABLES)
        require(isinstance(result, str) and result != "accepted",
                f"{prefix}: mutation {name} must name a typed rejection")
        kind, _, reason = result.partition(":")
        require(kind in tables and reason in tables[kind],
                f"{prefix}: mutation {name} names an unknown {stage} rejection {result!r}")


def validate(manifest: dict) -> list[dict]:
    native.inputs()  # validates the separately retained native boot provenance
    seen: set = set()
    for case in manifest["cases"]:
        try:
            validate_case(case, seen)
        except (ValueError, OSError) as error:
            case_id = case.get("id", "unknown") if isinstance(case, dict) else "unknown"
            raise CorpusError(f"case {case_id}: {error}") from error
    return manifest["cases"]


# --- conversion -----------------------------------------------------------

def read_memmap(path: Path) -> list[tuple[int, int, int]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    require(lines and lines[0] == "index\tstart\tend\ttype", f"{path}: unexpected header")
    entries = []
    for number, line in enumerate(lines[1:]):
        fields = line.split("\t")
        require(len(fields) == 4 and fields[0] == str(number), f"{path}: row {number} is malformed")
        start, end = int(fields[1], 16), int(fields[2], 16)
        require(end >= start, f"{path}: row {number} ends before it starts")
        require(0 <= start <= end < 2**64 and end-start+1 < 2**64,
                f"{path}: row {number} is outside the unsigned 64-bit capture range")
        require(fields[3] in E820_TYPES, f"{path}: row {number} has unknown E820 type {fields[3]!r}")
        entries.append((start, end - start + 1, E820_TYPES[fields[3]]))
    require(entries, f"{path}: no memory map entries")
    return entries


def handoff_variants(info: bytes) -> dict[str, bytes]:
    """Controlled memory-map changes; retain every row without sorting/merging."""
    tag_size = struct.unpack_from("<I", info, 12)[0]
    start, end = 24, 8 + tag_size
    entries = [info[offset:offset+ENTRY_SIZE] for offset in range(start, end, ENTRY_SIZE)]
    require(len(entries) >= 2, "memory variants need at least two captured entries")
    reversed_info = info[:start] + b"".join(reversed(entries)) + info[end:]
    overlapping = bytearray(info)
    base, length = struct.unpack_from("<QQ", info, start)
    struct.pack_into("<Q", overlapping, start+ENTRY_SIZE, base+min(4096, max(length-1, 0)))
    return {"handoff-order-reversed": reversed_info,
            "handoff-overlapping-entry": bytes(overlapping)}


def multiboot2_information(entries: list[tuple[int, int, int]]) -> bytes:
    """Wrap the captured entries, in captured order, into a Multiboot2
    information structure holding one memory-map tag and the end tag."""
    body = b"".join(struct.pack("<QQII", base, length, kind, 0) for base, length, kind in entries)
    tag_size = 16 + len(body)
    tag = struct.pack("<IIII", MEMORY_MAP_TAG, tag_size, ENTRY_SIZE, ENTRY_VERSION) + body
    tag += b"\0" * (-tag_size % 8)
    end = struct.pack("<II", END_TAG, 8)
    total = 8 + len(tag) + len(end)
    require(total <= MAX_TAG_BYTES, "memory map exceeds the decoder's tag byte bound")
    return struct.pack("<II", total, 0) + tag + end


def madt_bytes(path: Path) -> bytes:
    table = path.read_bytes()
    require(table[:4] == b"APIC", f"{path}: not an APIC (MADT) table")
    return table


def sdt_checksum_fix(table: bytearray) -> bytearray:
    table[9] = 0
    table[9] = (-sum(table)) % 256
    return table


# Controlled mutations derived from each case. Handoff mutations edit the
# information structure; MADT mutations edit the complete table (repairing
# only the checksum when the mutation is not itself about the checksum, so the
# named error is the one under test). Each case pins the typed rejection its
# mutation must produce.
def mutate_handoff(name: str, info: bytes) -> bytes:
    data = bytearray(info)
    if name == "handoff-truncated":
        return bytes(data[:-1])
    if name == "handoff-declared-size":
        struct.pack_into("<I", data, 0, len(data) + 8)
        return bytes(data)
    if name == "handoff-reserved":
        struct.pack_into("<I", data, 4, 1)
        return bytes(data)
    if name == "handoff-missing-end-tag":
        struct.pack_into("<I", data, len(data) - 8, 42)
        return bytes(data)
    if name == "handoff-entry-reserved":
        struct.pack_into("<I", data, 8 + 16 + 20, 1)
        return bytes(data)
    if name == "handoff-zero-length-entry":
        struct.pack_into("<Q", data, 8 + 16 + 8, 0)
        return bytes(data)
    if name == "handoff-entry-overflow":
        struct.pack_into("<QQ", data, 8 + 16, 0xFFFFFFFFFFFFF000, 0x2000)
        return bytes(data)
    if name == "handoff-entry-version":
        struct.pack_into("<I", data, 8 + 12, 1)
        return bytes(data)
    raise CorpusError(f"unknown handoff mutation {name}")


def mutate_madt(name: str, table: bytes) -> bytes:
    data = bytearray(table)
    if name == "madt-checksum":
        data[9] ^= 0x5A
        return bytes(data)
    if name == "madt-signature":
        data[0] = ord("X")
        return bytes(sdt_checksum_fix(data))
    if name == "madt-declared-length":
        struct.pack_into("<I", data, 4, len(data) + 1)
        return bytes(sdt_checksum_fix(data))
    if name == "madt-truncated":
        return bytes(sdt_checksum_fix(data[:-1]))
    if name == "madt-unknown-record":
        data += bytes([9, 16]) + b"\0" * 14
        struct.pack_into("<I", data, 4, len(data))
        return bytes(sdt_checksum_fix(data))
    if name == "madt-header-only":
        data = data[:40]
        struct.pack_into("<I", data, 4, 40)
        return bytes(sdt_checksum_fix(data))
    raise CorpusError(f"unknown MADT mutation {name}")


MUTATIONS = {
    "handoff-truncated": "handoff", "handoff-declared-size": "handoff",
    "handoff-reserved": "handoff", "handoff-missing-end-tag": "handoff",
    "handoff-entry-reserved": "handoff", "handoff-zero-length-entry": "handoff",
    "handoff-entry-overflow": "handoff", "handoff-entry-version": "handoff",
    "madt-checksum": "madt", "madt-signature": "madt", "madt-declared-length": "madt",
    "madt-truncated": "madt", "madt-unknown-record": "madt", "madt-header-only": "madt",
}
# Replayed word counts: the manifest pins the words that carry information
# (the projection stops at the last nonzero word) and every replay reads three
# more, which the boundary defines as zero; a rejected MADT has exactly five.
HANDOFF_TAIL = 3
MADT_WORDS = 5
MAX_HANDOFF_WORDS = 5 + 3 * (256 + 512)


def padded_words(stage: str, words: list[int]) -> list[int]:
    if stage == "madt":
        return list(words) + [0] * (MADT_WORDS - len(words))
    trimmed = list(words)
    while len(trimmed) > 3 and trimmed[-1] == 0:
        trimmed.pop()
    return trimmed + [0] * HANDOFF_TAIL


def result_words(stage: str, result: str, tables: dict) -> list[int]:
    kind, _, reason = result.partition(":")
    status = STATUS_DECODER if kind == "decoder-rejected" else STATUS_POLICY
    return padded_words(stage, [1, status, tables[kind][reason]])


def normalize(cases: list[dict], out: Path) -> list[dict]:
    """Write every normalized input under `out` and return the replay rows:
    one per case stage and one per mutation."""
    rows = []
    for case in cases:
        directory = CORPUS / case["id"]
        target = out / case["id"]
        target.mkdir(parents=True, exist_ok=True)
        info = multiboot2_information(read_memmap(directory / "memmap.tsv"))
        table = madt_bytes(directory / "acpi/APIC.bin")
        for stage, data in (("handoff", info), ("madt", table)):
            path = target / f"{stage}.bin"
            path.write_bytes(data)
            entry = case["expected"][stage]
            require(hashlib.sha256(data).hexdigest() == entry["normalized_sha256"],
                    f"case {case['id']}: normalized {stage} bytes differ from the recorded sha256")
            words = list(entry["words"])
            limit = MAX_HANDOFF_WORDS if stage == "handoff" else MADT_WORDS
            require(len(words) <= limit, f"case {case['id']}: too many {stage} words")
            rows.append({"case": case["id"], "input": f"{case['id']}/{stage}", "stage": stage,
                         "path": path, "words": padded_words(stage, words), "result": entry["result"]})
        for name, data in handoff_variants(info).items():
            entry = case["handoff_variants"][name]
            require(hashlib.sha256(data).hexdigest() == entry["normalized_sha256"],
                    f"case {case['id']}: normalized {name} bytes differ from the recorded sha256")
            path = target / f"{name}.bin"
            path.write_bytes(data)
            rows.append({"case": case["id"], "input": f"{case['id']}/{name}", "stage": "handoff",
                         "path": path, "words": padded_words("handoff", entry["words"]), "result": entry["result"]})
        if case["root_tables"] in ("acpidump", "freebsd-physical"):
            base = roots.from_capture(directory, info)
            for name, replay in {"root": base, **roots.mutations(base)}.items():
                entry = case["root_replay"] if name == "root" else case["root_mutations"][name]
                require(replay.digest() == entry["normalized_sha256"],
                        f"case {case['id']}: normalized {name} bytes differ from the recorded sha256")
                path = replay.write(target / name)
                rows.append({"case": case["id"], "input": f"{case['id']}/{name}", "stage": "root",
                             "path": path, "words": entry["words"], "result": entry["result"], "root": replay})
        for name, stage in MUTATIONS.items():
            data = mutate_handoff(name, info) if stage == "handoff" else mutate_madt(name, table)
            path = target / f"{name}.bin"
            path.write_bytes(data)
            tables = HANDOFF_RESULT_TABLES if stage == "handoff" else MADT_RESULT_TABLES
            rows.append({"case": case["id"], "input": f"{case['id']}/{name}", "stage": stage,
                         "path": path, "words": result_words(stage, case["mutations"][name], tables),
                         "result": case["mutations"][name]})
    import native_firmware_root_corpus as native_root
    rows.extend(native_root.rows(out))
    return rows + native.rows(out)


def write_replay(rows: list[dict], cases: list[dict], out: Path) -> None:
    """The hosted harness driver: one row per input with the boundary
    arguments and every expected result word."""
    ids = {case["id"]: case["apic"] for case in cases}
    with (out / "replay.tsv").open("w", encoding="utf-8") as handle:
        handle.write("# input\tstage\tfile\targ0\targ1\twords\n")
        for row in rows:
            if row["stage"] == "handoff":
                arg0, arg1 = row.get("handoff_args", (MULTIBOOT2_MAGIC, INFO_ADDRESS))
            elif "executing" in row:
                arg0, arg1 = 0, row["executing"]
            else:
                arg0, arg1 = ids[row["case"]]["bsp"], ids[row["case"]]["executing"]
            if row["stage"] == "root" and row["root"].executing_override is not None:
                arg1 = row["root"].executing_override
            handle.write("\t".join([row["input"], row["stage"], str(row["path"].resolve()), str(arg0),
                                    str(arg1), ",".join(str(word) for word in row["words"])]) + "\n")


def lean_bytes(data: bytes) -> str:
    return "⟨#[" + ", ".join(str(byte) for byte in data) + "]⟩"


def write_lean(rows: list[dict], cases: list[dict], out: Path) -> None:
    """Lean checks: the model's own query on the same bytes must return the
    manifest words. `native_decide` evaluates the compiled definitions."""
    ids = {case["id"]: case["apic"] for case in cases}
    lines = ["import LeanOS.BootMemoryMapDecoderABI", "import LeanOS.BootTopology", "",
             "/-! Generated by scripts/firmware-corpus.py from firmware-corpus/manifest.json. -/",
             "namespace LeanOS.FirmwareCorpus", "set_option maxRecDepth 8192", "set_option maxHeartbeats 2000000", ""]
    for index, row in enumerate(rows):
        words = row["words"]
        if row["stage"] != "root":
            data = row["path"].read_bytes()
            lines.append(f"def input{index} : ByteArray := {lean_bytes(data)}")
        if row["stage"] == "root":
            definitions, query = roots.lean_definitions(row["root"], row["executing"] if "executing" in row else ids[row["case"]]["executing"], f"rootInput{index}")
            lines.extend(definitions)
        elif row["stage"] == "handoff":
            magic, address = row.get("handoff_args", (MULTIBOOT2_MAGIC, INFO_ADDRESS))
            query = f"BootMemoryMapDecoderABI.query {magic} {address} input{index}"
        else:
            apic = ids[row["case"]]
            query = f"BootTopology.completeTopologyQuery input{index} {apic['bsp']} {apic['executing']}"
        expected = ", ".join(str(word) for word in words)
        lines.append(f"-- {row['input']}: {row['result']}")
        lines.append(f"example : (List.range {len(words)}).map (fun word => {query} (UInt64.ofNat word)) = [{expected}] := by")
        lines.append("  native_decide")
        lines.append("")
    lines.extend(roots.lean_bounds())
    lines.append("end LeanOS.FirmwareCorpus")
    (out / "Corpus.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_evaluate(cases: list[dict], out: Path) -> None:
    """Authoring aid: a Lean file that prints the model's words for every
    case stage and mutation, for review before pinning them in the manifest."""
    lines = ["import LeanOS.BootMemoryMapDecoderABI", "import LeanOS.BootTopology", "",
             "namespace LeanOS.FirmwareCorpusEvaluate", "",
             "/-- Drop trailing zero words, keeping at least the three status words. -/",
             "def trim (words : List UInt64) : List UInt64 :=",
             "  let reversed := words.reverse.dropWhile (fun word => word == 0)",
             "  if reversed.length < 3 then words.take 3 else reversed.reverse", ""]
    for case in cases:
        directory = CORPUS / case["id"]
        info = multiboot2_information(read_memmap(directory / "memmap.tsv"))
        table = madt_bytes(directory / "acpi/APIC.bin")
        apic = case["apic"]
        inputs = [("handoff", info), ("madt", table)] + list(handoff_variants(info).items())
        inputs += [(name, mutate_handoff(name, info) if stage == "handoff" else mutate_madt(name, table))
                   for name, stage in MUTATIONS.items()]
        for name, data in inputs:
            stage = "madt" if name == "madt" or name.startswith("madt-") else "handoff"
            ident = re.sub(r"[^A-Za-z0-9]", "_", f"{case['id']}_{name}")
            lines.append(f"def {ident} : ByteArray := {lean_bytes(data)}")
            if stage == "handoff":
                query = f"BootMemoryMapDecoderABI.query {MULTIBOOT2_MAGIC} {INFO_ADDRESS} {ident}"
                # Ask the model for the complete projection length. Replaying
                # every maximum-sized slot repeatedly normalizes the same map
                # thousands of times, even for small captures.
                lines.append(f"def {ident}_query := {query}")
                query = f"{ident}_query"
                count = (f"(if {query} 1 == 1 then 5 + 3 * "
                         f"(({query} 3).toNat + ({query} 4).toNat) + {HANDOFF_TAIL} else 3)")
            else:
                query = f"BootTopology.completeTopologyQuery {ident} {apic['bsp']} {apic['executing']}"
                count = MADT_WORDS
            lines.append(f'#eval IO.println s!"{case["id"]}\\t{name}\\t{{(trim ((List.range {count}).map (fun word => {query} (UInt64.ofNat word)))).toString}}"')
            lines.append("")
        if case.get("root_tables") in ("acpidump", "freebsd-physical"):
            root = roots.from_capture(directory, info)
            for name, replay in {"root": root, **roots.mutations(root)}.items():
                query = roots.lean_query(replay, apic["executing"])
                lines.append(f'#eval IO.println s!"{case["id"]}\\t{name}\\t{{((List.range 5).map (fun word => {query} (UInt64.ofNat word))).toString}}"')
                lines.append(f'#eval IO.println s!"{case["id"]}\\t{name}\\tsha256-input\\t{replay.digest()}"')
        for name, data in inputs:
            lines.append(f'#eval IO.println s!"{case["id"]}\\t{name}\\tsha256-input\\t{hashlib.sha256(data).hexdigest()}"')
    lines.append("end LeanOS.FirmwareCorpusEvaluate")
    (out / "Evaluate.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")


def name_of(stage: str, words: list[int]) -> str:
    if stage == "root" and words[1] == STATUS_DECODER:
        return roots.rejection_name(words)
    tables = HANDOFF_RESULT_TABLES if stage == "handoff" else MADT_RESULT_TABLES
    if words[1] == STATUS_ACCEPTED:
        return "accepted"
    kind = "decoder-rejected" if words[1] == STATUS_DECODER else (
        "normalizer-rejected" if stage == "handoff" else "admission-rejected")
    for reason, code in tables[kind].items():
        if code == words[2]:
            return f"{kind}:{reason}"
    raise CorpusError(f"{stage}: the model returned an unlisted rejection code {words[2]}")


def pin(manifest: dict, evaluation: Path, path: Path) -> None:
    """Authoring step: fill each case's words, normalized digests, and
    mutation results from the Lean evaluation output, refusing any case whose
    declared result name disagrees with what the model computed."""
    words: dict[tuple[str, str], list[int]] = {}
    digests: dict[tuple[str, str], str] = {}
    for line in evaluation.read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        if len(fields) == 4 and fields[2] == "sha256-input":
            digests[(fields[0], fields[1])] = fields[3]
        elif len(fields) == 3 and fields[2].startswith("["):
            words[(fields[0], fields[1])] = [int(word) for word in fields[2].strip("[]").split(",") if word.strip()]
    for case in manifest["cases"]:
        case_id = case["id"]
        stages = ("handoff", "madt", "root") if case.get("root_tables") in ("acpidump", "freebsd-physical") else ("handoff", "madt")
        for stage in stages:
            key = (case_id, stage)
            require(key in words and key in digests, f"case {case_id}: evaluation lacks the {stage} stage")
            computed = name_of(stage, words[key])
            entry = case["root_replay"] if stage == "root" else case["expected"][stage]
            declared = entry["result"]
            require(computed == declared,
                    f"case {case_id}: declared {stage} result {declared!r} but the model computes {computed!r}")
            entry["words"] = words[key]
            entry["normalized_sha256"] = digests[key]
        if case.get("root_tables") in ("acpidump", "freebsd-physical"):
            root = roots.from_capture(CORPUS / case_id, multiboot2_information(read_memmap(CORPUS / case_id / "memmap.tsv")))
            case["root_mutations"] = {}
            for name in roots.mutations(root):
                key = (case_id, name)
                require(key in words and key in digests, f"case {case_id}: evaluation lacks root mutation {name}")
                computed = name_of("root", words[key])
                require(computed != "accepted", f"case {case_id}: root mutation {name} was accepted")
                case["root_mutations"][name] = {"result": computed, "words": words[key], "normalized_sha256": digests[key]}
        case["handoff_variants"] = {}
        for name in ("handoff-order-reversed", "handoff-overlapping-entry"):
            key = (case_id, name)
            require(key in words and key in digests, f"case {case_id}: evaluation lacks memory variant {name}")
            case["handoff_variants"][name] = {"result": name_of("handoff", words[key]),
                                             "words": words[key], "normalized_sha256": digests[key]}
        case["mutations"] = {}
        for name, stage in MUTATIONS.items():
            key = (case_id, name)
            require(key in words, f"case {case_id}: evaluation lacks mutation {name}")
            computed = name_of(stage, words[key])
            require(computed != "accepted", f"case {case_id}: mutation {name} was accepted by the model")
            case["mutations"][name] = computed
    path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--manifest", type=Path, default=MANIFEST)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("validate", help="check the manifest, hashes, and expectation vocabulary")
    sub.add_parser("list", help="print case ids and their declared results")
    normalize_parser = sub.add_parser("normalize", help="write normalized inputs, mutations, replay driver, and Lean checks")
    normalize_parser.add_argument("--out", type=Path, required=True)
    evaluate_parser = sub.add_parser("evaluate", help="write an authoring Lean file that prints the model's words")
    evaluate_parser.add_argument("--out", type=Path, required=True)
    pin_parser = sub.add_parser("pin", help="fill words and digests from a Lean evaluation log when they match the declared results")
    pin_parser.add_argument("--evaluation", type=Path, required=True)
    args = parser.parse_args()
    try:
        manifest = load_manifest(args.manifest)
        if args.command == "pin":
            pin(manifest, args.evaluation, args.manifest)
            print(f"pinned {len(manifest['cases'])} cases from {args.evaluation}")
            return 0
        if args.command == "evaluate":
            cases = manifest["cases"]
            for case in cases:
                require(isinstance(case.get("id"), str) and isinstance(case.get("apic"), dict),
                        "evaluate needs at least ids and apic identities")
            args.out.mkdir(parents=True, exist_ok=True)
            write_evaluate(cases, args.out)
            print(f"wrote {args.out / 'Evaluate.lean'}")
            return 0
        cases = validate(manifest)
        if args.command == "validate":
            print(f"firmware corpus manifest valid: {len(cases)} cases, {len(MUTATIONS)} mutations each")
        elif args.command == "list":
            for case in cases:
                print("\t".join([case["id"], case["profile"], case["expected"]["handoff"]["result"],
                                 case["expected"]["madt"]["result"]]))
        elif args.command == "normalize":
            args.out.mkdir(parents=True, exist_ok=True)
            rows = normalize(cases, args.out)
            write_replay(rows, cases, args.out)
            write_lean(rows, cases, args.out)
            print(f"normalized {len(cases)} cases into {len(rows)} replay rows under {args.out}")
    except (CorpusError, ValueError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
