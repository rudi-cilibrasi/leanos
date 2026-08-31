#!/usr/bin/env python3
"""Run and verify LeanOS's versioned, release-blocking QEMU evidence matrix."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tarfile
import tempfile
import time


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MATRIX = ROOT / "scripts/emulator-evidence-matrix.tsv"
DEFAULT_BUILD = ROOT / "build/boot"
DEFAULT_OUTPUT = ROOT / "build/evidence/emulator-evidence.json"
DEFAULT_TOOLS = ROOT / "build/ci/tool-versions.txt"
DEFAULT_BUNDLE = ROOT / "build/ci/emulator-evidence.tar"
BUNDLE_ROOTS = (
    "build/boot",
    "build/evidence",
    "build/ci",
    "build/oracle",
    "build/boot-handoff-host",
    "build/boot-topology-host",
    "build/boot-handoff-stream",
)
BUNDLE_CONTEXT_FILES = (
    "docs/page-fault-snapshot.md",
    "scripts/emulator-evidence-matrix.tsv",
    "scripts/hosted-generated-boundaries.tsv",
)
BUNDLE_REQUIRED_FILES = (
    "build/boot/SHA256SUMS",
    "build/boot/SOURCE_REVISION",
    "build/ci/emulator-evidence.log",
    "build/ci/image-build.log",
    "build/ci/tool-versions.txt",
    "build/evidence/q35-edu-dma.tsv",
    "build/evidence/q35-pci-construction.tsv",
)
REQUIRED_FAULT_RELEASE_ARTIFACTS = (
    (
        "build/boot/leanos-${version}-x86_64-fault-containment.iso",
        "leanos-${version}-x86_64-fault-containment.iso",
    ),
    (
        "build/boot/leanos-fault-containment.elf",
        "leanos-${version}-x86_64-fault-containment.elf",
    ),
    (
        "build/boot/leanos-fault-containment.map",
        "leanos-${version}-x86_64-fault-containment.map",
    ),
    (
        "build/boot/fault-containment.serial.log",
        "leanos-${version}-fault-containment-serial.log",
    ),
    (
        "build/boot/fault-containment.disassembly.txt",
        "leanos-${version}-fault-containment-disassembly.txt",
    ),
    (
        "build/boot/fault-containment-policy-report.txt",
        "leanos-${version}-fault-containment-policy-report.txt",
    ),
    (
        "build/boot/fault-containment-snapshot.txt",
        "leanos-${version}-fault-containment-snapshot.txt",
    ),
    (
        "build/boot/boot-page-plan-fault-containment.final.h",
        "leanos-${version}-fault-containment-page-plan.h",
    ),
    (
        "build/boot/leanos-${version}-x86_64-fault-readonly-write.iso",
        "leanos-${version}-x86_64-fault-readonly-write.iso",
    ),
    (
        "build/boot/leanos-fault-readonly-write.elf",
        "leanos-${version}-x86_64-fault-readonly-write.elf",
    ),
    (
        "build/boot/leanos-fault-readonly-write.map",
        "leanos-${version}-x86_64-fault-readonly-write.map",
    ),
    (
        "build/boot/fault-readonly-write.serial.log",
        "leanos-${version}-fault-readonly-write-serial.log",
    ),
    (
        "build/boot/fault-readonly-write.disassembly.txt",
        "leanos-${version}-fault-readonly-write-disassembly.txt",
    ),
    (
        "build/boot/fault-readonly-write-policy-report.txt",
        "leanos-${version}-fault-readonly-write-policy-report.txt",
    ),
    (
        "build/boot/fault-readonly-write-snapshot.txt",
        "leanos-${version}-fault-readonly-write-snapshot.txt",
    ),
    (
        "build/boot/boot-page-plan-fault-readonly-write.final.h",
        "leanos-${version}-fault-readonly-write-page-plan.h",
    ),
    (
        "build/boot/leanos-${version}-x86_64-fault-nx-execute.iso",
        "leanos-${version}-x86_64-fault-nx-execute.iso",
    ),
    (
        "build/boot/leanos-fault-nx-execute.elf",
        "leanos-${version}-x86_64-fault-nx-execute.elf",
    ),
    (
        "build/boot/leanos-fault-nx-execute.map",
        "leanos-${version}-x86_64-fault-nx-execute.map",
    ),
    (
        "build/boot/fault-nx-execute.serial.log",
        "leanos-${version}-fault-nx-execute-serial.log",
    ),
    (
        "build/boot/fault-nx-execute.disassembly.txt",
        "leanos-${version}-fault-nx-execute-disassembly.txt",
    ),
    (
        "build/boot/fault-nx-execute-policy-report.txt",
        "leanos-${version}-fault-nx-execute-policy-report.txt",
    ),
    (
        "build/boot/fault-nx-execute-snapshot.txt",
        "leanos-${version}-fault-nx-execute-snapshot.txt",
    ),
    (
        "build/boot/boot-page-plan-fault-nx-execute.final.h",
        "leanos-${version}-fault-nx-execute-page-plan.h",
    ),
)
REQUIRED_FAULT_RELEASE_ARTIFACTS += tuple(
    (
        source.replace("@PROBE@", probe),
        destination.replace("@PROBE@", probe),
    )
    for probe in ("reserved-bit", "walk-mismatch")
    for source, destination in (
        (
            "build/boot/leanos-${version}-x86_64-fault-@PROBE@.iso",
            "leanos-${version}-x86_64-fault-@PROBE@.iso",
        ),
        (
            "build/boot/leanos-fault-@PROBE@.elf",
            "leanos-${version}-x86_64-fault-@PROBE@.elf",
        ),
        (
            "build/boot/leanos-fault-@PROBE@.map",
            "leanos-${version}-x86_64-fault-@PROBE@.map",
        ),
        (
            "build/boot/fault-@PROBE@.serial.log",
            "leanos-${version}-fault-@PROBE@-serial.log",
        ),
        (
            "build/boot/fault-@PROBE@.disassembly.txt",
            "leanos-${version}-fault-@PROBE@-disassembly.txt",
        ),
        (
            "build/boot/fault-@PROBE@-policy-report.txt",
            "leanos-${version}-fault-@PROBE@-policy-report.txt",
        ),
        (
            "build/boot/fault-@PROBE@-terminal.txt",
            "leanos-${version}-fault-@PROBE@-terminal.txt",
        ),
        (
            "build/boot/boot-page-plan-fault-@PROBE@.final.h",
            "leanos-${version}-fault-@PROBE@-page-plan.h",
        ),
    )
)
RESULT_CLASSES = {"accepted-boot", "controlled-rejection", "fail-stop"}
TIERS = {"pr", "evidence"}
RUNNERS = {
    "boot",
    "assigned-edu",
    "fault-integrity",
    "return",
    "peer-pke",
    "double-fault",
    "entry-stack-overflow",
    "nmi",
    "multivcpu",
    "bootstrap32-ud",
    "bootstrap64-nmi",
    "double-fault-guard",
    "malformed-handoff",
}
RUNNER_RESULT_CLASSES = {
    "boot": "accepted-boot",
    "assigned-edu": "accepted-boot",
    "fault-integrity": "fail-stop",
    "return": "controlled-rejection",
    "peer-pke": "controlled-rejection",
    "double-fault": "fail-stop",
    "entry-stack-overflow": "fail-stop",
    "nmi": "fail-stop",
    "multivcpu": "controlled-rejection",
    "bootstrap32-ud": "fail-stop",
    "bootstrap64-nmi": "fail-stop",
    "double-fault-guard": "controlled-rejection",
    "malformed-handoff": "controlled-rejection",
}
REQUIRED_IOTLB_ORACLE_ROWS = (
    "iotlb.observe-filled",
    "iotlb.prepare-retains-live",
    "iotlb.reject-stale-ticket",
    "iotlb.reject-wrong-source",
    "iotlb.reject-wrong-domain",
    "iotlb.reject-wrong-mapping",
    "iotlb.reject-wrong-iova",
    "iotlb.ack-exact",
    "iotlb.reject-completion-replay",
)
REQUIRED_FAST_ENTRY_ROWS = {
    "fast-entry-syscall": {
        "runner": "boot",
        "result_class": "accepted-boot",
        "timeout": "30",
        "image": "leanos-@VERSION@-x86_64-fast-entry-syscall.iso",
        "elf": "leanos-fast-entry-syscall.elf",
        "serial_log": "fast-entry-syscall.serial.log",
        "scenario": "fast-entry-syscall",
        "mode": "-",
        "reason": "-",
    },
    "fast-entry-sysenter": {
        "runner": "boot",
        "result_class": "accepted-boot",
        "timeout": "30",
        "image": "leanos-@VERSION@-x86_64-fast-entry-sysenter.iso",
        "elf": "leanos-fast-entry-sysenter.elf",
        "serial_log": "fast-entry-sysenter.serial.log",
        "scenario": "fast-entry-sysenter",
        "mode": "-",
        "reason": "-",
    },
    "return-fast-entry-sce-relaxation": {
        "runner": "return",
        "result_class": "controlled-rejection",
        "timeout": "30",
        "image": "leanos-@VERSION@-x86_64-return-fast-entry-sce-relaxation.iso",
        "elf": "leanos-return-fast-entry-sce-relaxation.elf",
        "serial_log": "return-corruption-fast-entry-sce-relaxation.serial.log",
        "scenario": "fast-entry-sce-relaxation",
        "mode": "14",
        "reason": "fast-entry-efer-readback",
    },
    "return-fast-entry-lstar-relaxation": {
        "runner": "return",
        "result_class": "controlled-rejection",
        "timeout": "30",
        "image": "leanos-@VERSION@-x86_64-return-fast-entry-lstar-relaxation.iso",
        "elf": "leanos-return-fast-entry-lstar-relaxation.elf",
        "serial_log": "return-corruption-fast-entry-lstar-relaxation.serial.log",
        "scenario": "fast-entry-lstar-relaxation",
        "mode": "15",
        "reason": "fast-entry-target-readback",
    },
    "return-fast-entry-sysenter-eip-relaxation": {
        "runner": "return",
        "result_class": "controlled-rejection",
        "timeout": "30",
        "image": "leanos-@VERSION@-x86_64-return-fast-entry-sysenter-eip-relaxation.iso",
        "elf": "leanos-return-fast-entry-sysenter-eip-relaxation.elf",
        "serial_log": "return-corruption-fast-entry-sysenter-eip-relaxation.serial.log",
        "scenario": "fast-entry-sysenter-eip-relaxation",
        "mode": "16",
        "reason": "fast-entry-target-readback",
    },
}
REQUIRED_FAULT_INTEGRITY_ROWS = {
    "fault-reserved-bit": {
        "runner": "fault-integrity",
        "result_class": "fail-stop",
        "timeout": "30",
        "image": "leanos-@VERSION@-x86_64-fault-reserved-bit.iso",
        "elf": "leanos-fault-reserved-bit.elf",
        "serial_log": "fault-reserved-bit.serial.log",
        "scenario": "reserved-bit",
        "mode": "-",
        "reason": "page-table-integrity",
    },
    "fault-walk-mismatch": {
        "runner": "fault-integrity",
        "result_class": "fail-stop",
        "timeout": "30",
        "image": "leanos-@VERSION@-x86_64-fault-walk-mismatch.iso",
        "elf": "leanos-fault-walk-mismatch.elf",
        "serial_log": "fault-walk-mismatch.serial.log",
        "scenario": "walk-mismatch",
        "mode": "-",
        "reason": "error-address-walk-disagreement",
    },
}
for mechanism, mode in (
    ("star", "17"),
    ("cstar", "18"),
    ("sfmask", "19"),
    ("sysenter-cs", "20"),
    ("sysenter-esp", "21"),
):
    scenario = f"fast-entry-{mechanism}-relaxation"
    REQUIRED_FAST_ENTRY_ROWS[f"return-{scenario}"] = {
        "runner": "return",
        "result_class": "controlled-rejection",
        "timeout": "30",
        "image": f"leanos-@VERSION@-x86_64-return-{scenario}.iso",
        "elf": f"leanos-return-{scenario}.elf",
        "serial_log": f"return-corruption-{scenario}.serial.log",
        "scenario": scenario,
        "mode": mode,
        "reason": "fast-entry-target-readback",
    }


class EvidenceError(RuntimeError):
    pass


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def display_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(ROOT))
    except ValueError:
        return str(resolved)


def resolve_recorded(path: str) -> Path:
    candidate = Path(path)
    return candidate if candidate.is_absolute() else ROOT / candidate


def git_revision() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()


def qemu_version(environment: dict[str, str]) -> str:
    qemu = environment.get("LEANOS_QEMU", "qemu-system-x86_64")
    try:
        output = subprocess.check_output(
            [qemu, "--version"], cwd=ROOT, env=environment,
            stderr=subprocess.STDOUT, text=True,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise EvidenceError(f"cannot record QEMU version for {qemu!r}: {error}")
    first = output.splitlines()
    if not first:
        raise EvidenceError(f"QEMU version command for {qemu!r} returned no output")
    return first[0]


def qemu_accelerator(environment: dict[str, str]) -> str:
    accelerator = environment.get("LEANOS_QEMU_ACCELERATOR", "tcg")
    if accelerator not in {"tcg", "kvm"}:
        raise EvidenceError(
            "QEMU accelerator must be exactly 'tcg' or 'kvm'; fallback lists are forbidden"
        )
    return accelerator


def parse_matrix(path: Path) -> tuple[str, list[dict[str, str]]]:
    if not path.is_file():
        raise EvidenceError(f"matrix not found: {display_path(path)}")
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or not re.fullmatch(r"# leanos-emulator-evidence-v[0-9]+", lines[0]):
        raise EvidenceError("matrix lacks a versioned first-line identifier")
    matrix_id = lines[0][2:]
    mandatory_lines = [line for line in lines[1:] if line.startswith("# mandatory-count\t")]
    if len(mandatory_lines) != 1:
        raise EvidenceError("matrix must declare exactly one mandatory count")
    mandatory_text = mandatory_lines[0].split("\t", 1)[1]
    if not mandatory_text.isdigit() or int(mandatory_text) < 1:
        raise EvidenceError("matrix has an invalid mandatory count")
    mandatory_count = int(mandatory_text)
    rows: list[dict[str, str]] = []
    keys = (
        "id", "runner", "result_class", "timeout", "image", "elf",
        "serial_log", "scenario", "mode", "reason", "tier",
    )
    for number, line in enumerate(lines[1:], 2):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != len(keys):
            raise EvidenceError(
                f"matrix line {number} has {len(fields)} fields; expected {len(keys)}"
            )
        row = dict(zip(keys, fields, strict=True))
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", row["id"]):
            raise EvidenceError(f"matrix line {number} has invalid scenario ID")
        if row["runner"] not in RUNNERS:
            raise EvidenceError(
                f"scenario {row['id']} has unrecognized runner {row['runner']!r}"
            )
        if row["result_class"] not in RESULT_CLASSES:
            raise EvidenceError(
                f"scenario {row['id']} has unrecognized result class "
                f"{row['result_class']!r}"
            )
        if row["result_class"] != RUNNER_RESULT_CLASSES[row["runner"]]:
            raise EvidenceError(
                f"scenario {row['id']} result class does not match its runner"
            )
        if row["tier"] not in TIERS:
            raise EvidenceError(
                f"scenario {row['id']} has unrecognized tier {row['tier']!r}"
            )
        if not row["timeout"].isdigit() or int(row["timeout"]) < 1:
            raise EvidenceError(f"scenario {row['id']} has invalid timeout")
        for key in ("image", "elf", "serial_log"):
            if Path(row[key]).name != row[key] or row[key] in {"", ".", ".."}:
                raise EvidenceError(f"scenario {row['id']} has unsafe {key} path")
        rows.append(row)

    ids = [row["id"] for row in rows]
    duplicates = sorted({scenario_id for scenario_id in ids if ids.count(scenario_id) > 1})
    if duplicates:
        raise EvidenceError(f"duplicate scenario ID(s): {', '.join(duplicates)}")
    if matrix_id != "leanos-emulator-evidence-v2":
        raise EvidenceError(f"unsupported matrix version: {matrix_id}")
    if len(rows) != mandatory_count:
        raise EvidenceError(
            f"mandatory inventory count differs: declared {mandatory_count}, found {len(rows)}"
        )
    pr_runner_counts = {
        runner: sum(
            row["runner"] == runner and row["tier"] == "pr" for row in rows
        )
        for runner in RUNNERS
    }
    invalid_pr_runner_counts = {
        runner: count
        for runner, count in sorted(pr_runner_counts.items())
        if count != 1
    }
    if invalid_pr_runner_counts:
        raise EvidenceError(
            "PR tier must contain exactly one scenario per runner; "
            f"counts={invalid_pr_runner_counts}"
        )

    rows_by_id = {row["id"]: row for row in rows}
    for scenario_id, expected in REQUIRED_FAST_ENTRY_ROWS.items():
        row = rows_by_id.get(scenario_id)
        if row is None:
            raise EvidenceError(
                f"mandatory fast-entry scenario is absent: {scenario_id}"
            )
        for key, value in expected.items():
            if row[key] != value:
                raise EvidenceError(
                    f"mandatory fast-entry scenario {scenario_id} has "
                    f"unexpected {key} {row[key]!r}"
                )
    for scenario_id, expected in REQUIRED_FAULT_INTEGRITY_ROWS.items():
        row = rows_by_id.get(scenario_id)
        if row is None:
            raise EvidenceError(
                f"mandatory fault-integrity scenario is absent: {scenario_id}"
            )
        for key, value in expected.items():
            if row[key] != value:
                raise EvidenceError(
                    f"mandatory fault-integrity scenario {scenario_id} has "
                    f"unexpected {key} {row[key]!r}"
                )

    serials = [row["serial_log"] for row in rows]
    if len(serials) != len(set(serials)):
        raise EvidenceError("matrix serial-log destinations are not unique")
    for key in ("image", "elf"):
        values = [row[key] for row in rows]
        if len(values) != len(set(values)):
            raise EvidenceError(f"matrix {key} artifacts are not unique")
    return matrix_id, rows


def select_rows(
    rows: list[dict[str, str]], scenario: str | None, tier: str,
    shard_index: int | None, shard_count: int | None,
) -> list[dict[str, str]]:
    """Select one scenario or a stable matrix-order shard."""
    if scenario is not None and tier != "all":
        raise EvidenceError("scenario selection cannot be combined with tier selection")
    if scenario is not None and (shard_index is not None or shard_count is not None):
        raise EvidenceError("scenario selection cannot be combined with sharding")
    if (shard_index is None) != (shard_count is None):
        raise EvidenceError("shard index and count must be specified together")
    if scenario is not None:
        selected = [row for row in rows if row["id"] == scenario]
        if not selected:
            raise EvidenceError(f"scenario is absent from matrix: {scenario}")
        return selected
    if tier == "pr":
        rows = [row for row in rows if row["tier"] == "pr"]
    elif tier != "all":
        raise EvidenceError(f"unrecognized evidence tier: {tier}")
    if shard_index is None or shard_count is None:
        return rows
    if shard_count < 1:
        raise EvidenceError("shard count must be a positive integer")
    if shard_index < 0 or shard_index >= shard_count:
        raise EvidenceError("shard index must be between zero and count minus one")
    selected = rows[shard_index::shard_count]
    if not selected:
        raise EvidenceError("selected shard is empty")
    return selected


def select_build_artifacts(
    rows: list[dict[str, str]], version: str,
) -> list[tuple[str, str, str, str, str]]:
    """Return the stable minimal image/ELF inventory for selected evidence rows."""
    if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", version):
        raise EvidenceError("version must be MAJOR.MINOR.PATCH")
    artifacts = []
    for row in rows:
        elf = row["elf"]
        if not re.fullmatch(r"leanos(?:-[a-z0-9-]+)?\.elf", elf):
            raise EvidenceError(
                f"scenario {row['id']} has unsupported build ELF {elf!r}"
            )
        prelink_target = elf.removesuffix(".elf") + "-prelink.elf"
        final_target = elf
        # These families intentionally finish outside the generated link graph:
        # assigned EDU converges its own page plan, while the double-fault
        # variants run policy-specific final links after their plans exist.
        # Name the graph prerequisite that is actually buildable at each phase
        # instead of deriving nonexistent Make targets from the packaged ELF.
        target_overrides = {
            "leanos-assigned-edu.elf": ("leanos-prelink.elf", "leanos.elf"),
            # The negative topology scenario runs the ordinary reviewed image;
            # its distinct matrix artifacts are aliases materialized after the
            # canonical image is built so matrix identity remains one-to-one.
            "leanos-multivcpu-rejection.elf": (
                "leanos-prelink.elf",
                "leanos.elf",
            ),
            "leanos-double-fault.elf": (
                "leanos-double-fault-prelink.elf",
                "kernel-double-fault.o",
            ),
            "leanos-entry-stack-overflow.elf": (
                "leanos-entry-stack-overflow-prelink.elf",
                "kernel-entry-stack-overflow.o",
            ),
            "leanos-double-fault-guard-mapped.elf": (
                "leanos-guard-prelink.elf",
                "kernel-double-fault-guard-mapped.o",
            ),
        }
        prelink_target, final_target = target_overrides.get(
            elf, (prelink_target, final_target)
        )
        artifacts.append((
            row["id"],
            row["runner"],
            row["image"].replace("@VERSION@", version),
            prelink_target,
            final_target,
        ))
    return artifacts


def print_build_plan(args: argparse.Namespace) -> None:
    """Emit a machine-readable build boundary before image construction."""
    _matrix_id, rows = parse_matrix(args.matrix.resolve())
    rows = select_rows(rows, None, args.tier, args.shard_index, args.shard_count)
    print("id\trunner\timage\tprelink_elf\tfinal_elf")
    for fields in select_build_artifacts(rows, args.version):
        print("\t".join(fields))


def expanded(row: dict[str, str], version: str, build_dir: Path) -> dict[str, Path]:
    paths = {
        key: build_dir / row[key].replace("@VERSION@", version)
        for key in ("image", "elf", "serial_log")
    }
    if row["runner"] in {"nmi", "multivcpu"}:
        paths["qmp_transcript"] = Path(str(paths["serial_log"]) + ".qmp.jsonl")
    if row["runner"] == "multivcpu":
        paths["multivcpu_inventory"] = Path(
            str(paths["serial_log"]) + ".qmp.tsv"
        )
    if row["runner"] == "boot":
        paths["dma_snapshot"] = (
            build_dir / f"dma-quarantine-snapshot-{row['scenario']}.tsv"
        )
        paths["vtd_snapshot"] = (
            build_dir / f"vtd-activation-snapshot-{row['scenario']}.tsv"
        )
    return paths


def scenario_invocation(
    row: dict[str, str], paths: dict[str, Path], build_dir: Path, version: str,
    accelerator: str = "tcg",
) -> tuple[list[str], dict[str, str]]:
    if accelerator not in {"tcg", "kvm"}:
        raise EvidenceError("scenario invocation received an invalid QEMU accelerator")
    environment = {
        "LEANOS_VERSION": version,
        "LEANOS_QEMU_TIMEOUT_SECONDS": row["timeout"],
        "LEANOS_QEMU_ACCELERATOR": accelerator,
        "LEANOS_SERIAL_LOG": str(paths["serial_log"]),
    }
    if row["runner"] == "boot":
        environment["LEANOS_BOOT_SCENARIO"] = row["scenario"]
        environment["LEANOS_DMA_SNAPSHOT"] = str(paths["dma_snapshot"])
        environment["LEANOS_VTD_SNAPSHOT"] = str(paths["vtd_snapshot"])
        environment["LEANOS_SOURCE_REVISION_FILE"] = str(build_dir / "SOURCE_REVISION")
        command = ["./scripts/run-image.sh", str(paths["image"])]
    elif row["runner"] == "assigned-edu":
        command = ["./scripts/run-assigned-edu.sh", str(paths["image"])]
    elif row["runner"] == "fault-integrity":
        environment["LEANOS_FAULT_INTEGRITY_PROBE"] = row["scenario"]
        environment["LEANOS_FAULT_INTEGRITY_ELF"] = str(paths["elf"])
        environment["LEANOS_FAULT_TERMINAL_ARTIFACT"] = str(
            build_dir / f"fault-{row['scenario']}-terminal.txt"
        )
        command = ["./scripts/run-fault-integrity.sh", str(paths["image"])]
    elif row["runner"] == "return":
        environment["LEANOS_BOOT_DIR"] = str(build_dir)
        environment["LEANOS_RETURN_CORRUPTION_FIXTURE"] = row["scenario"]
        command = ["./scripts/run-return-corruptions.sh"]
    elif row["runner"] == "peer-pke":
        environment["LEANOS_BOOT_DIR"] = str(build_dir)
        command = ["./scripts/run-extended-state-peer-pke.sh", str(paths["image"])]
    elif row["runner"] == "double-fault":
        command = ["./scripts/run-double-fault.sh", str(paths["image"])]
    elif row["runner"] == "entry-stack-overflow":
        command = ["./scripts/run-entry-stack-overflow.sh", str(paths["image"])]
    elif row["runner"] == "nmi":
        environment["LEANOS_NMI_SCENARIO"] = row["scenario"]
        environment["LEANOS_QMP_LOG"] = str(paths["qmp_transcript"])
        command = ["./scripts/run-nmi.sh", str(paths["image"])]
    elif row["runner"] == "multivcpu":
        environment["LEANOS_QMP_LOG"] = str(paths["qmp_transcript"])
        environment["LEANOS_MULTIVCPU_INVENTORY"] = str(
            paths["multivcpu_inventory"]
        )
        command = ["./scripts/run-multivcpu-rejection.sh", str(paths["image"])]
    elif row["runner"] == "bootstrap32-ud":
        command = ["./scripts/run-bootstrap32-ud.sh", str(paths["image"])]
    elif row["runner"] == "bootstrap64-nmi":
        command = ["./scripts/run-bootstrap64-nmi.sh", str(paths["image"])]
    elif row["runner"] == "malformed-handoff":
        environment["LEANOS_HANDOFF_REJECTION_REASON"] = row["reason"]
        command = ["./scripts/run-malformed-handoff.sh", str(paths["image"])]
    else:
        environment["LEANOS_EXPECT_GUARD_MAPPED"] = "1"
        command = ["./scripts/run-double-fault.sh", str(paths["image"])]
    return command, environment


def write_report(output: Path, report: dict[str, object]) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(output)


def base_report(
    matrix: Path, matrix_id: str, revision: str, source_file: Path,
    tools: Path, qemu: str, accelerator: str,
) -> dict[str, object]:
    return {
        "schema": "leanos-emulator-evidence-report-v1",
        "matrix": {
            "id": matrix_id,
            "path": display_path(matrix),
            "sha256": sha256(matrix),
        },
        "source": {
            "git_revision": revision,
            "embedded_revision_path": display_path(source_file),
            "embedded_revision_sha256": sha256(source_file),
        },
        "tools": {
            "inventory_path": display_path(tools),
            "inventory_sha256": sha256(tools),
            "inventory": tools.read_text(encoding="utf-8").splitlines(),
            "qemu_version": qemu,
            "python_version": sys.version.splitlines()[0],
        },
        "execution": {
            "requested_accelerator": accelerator,
            "fallback_allowed": False,
        },
        "results": [],
        "status": "RUNNING",
    }


def execute_scenario(
    row: dict[str, str], build_dir: Path, version: str,
    environment: dict[str, str],
) -> tuple[dict[str, Path], list[str], dict[str, str], str, int, float]:
    started = time.monotonic()
    paths = expanded(row, version, build_dir)
    command, scenario_environment = scenario_invocation(
        row, paths, build_dir, version, qemu_accelerator(environment)
    )
    for key in (
        "serial_log",
        "dma_snapshot",
        "vtd_snapshot",
        "qmp_transcript",
        "multivcpu_inventory",
    ):
        if key in paths:
            paths[key].unlink(missing_ok=True)
    combined_environment = environment.copy()
    combined_environment.update(scenario_environment)
    # Keep this root short: some runners create a nested AF_UNIX QMP socket,
    # whose full path must fit Linux's 108-byte sockaddr_un limit.
    with tempfile.TemporaryDirectory(prefix="le-") as scratch:
        combined_environment["TMPDIR"] = scratch
        try:
            completed = subprocess.run(
                command, cwd=ROOT, env=combined_environment, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=int(row["timeout"]) + 5, check=False,
            )
            command_output = completed.stdout
            status = completed.returncode
        except subprocess.TimeoutExpired as error:
            command_output = error.stdout or ""
            if isinstance(command_output, bytes):
                command_output = command_output.decode(errors="replace")
            command_output += (
                "\nfailure_class=matrix-timeout: scenario runner exceeded outer limit\n"
            )
            status = 124
    # Runner diagnostics may include randomized descendants of TMPDIR (for
    # example the bootstrap64 QMP socket created by mktemp).  Those paths are
    # execution details, not evidence identity; canonicalize them before the
    # command log and report are hashed so serial and parallel runs agree.
    command_output = command_output.replace(scratch, "$SCENARIO_TMPDIR")
    command_output = re.sub(
        r"(\$SCENARIO_TMPDIR)/tmp\.[^/\s'\"\\,]+",
        r"\1/$NESTED_TMPDIR",
        command_output,
    )
    return (
        paths, command, scenario_environment, command_output, status,
        time.monotonic() - started,
    )


def run(args: argparse.Namespace) -> None:
    matrix = args.matrix.resolve()
    build_dir = args.build_dir.resolve()
    output = args.output.resolve()
    tools = args.tool_versions.resolve()
    matrix_id, rows = parse_matrix(matrix)
    rows = select_rows(
        rows, args.scenario, args.tier, args.shard_index, args.shard_count
    )
    version = args.version
    if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", version):
        raise EvidenceError("version must be MAJOR.MINOR.PATCH")
    revision = git_revision()
    source_file = build_dir / "SOURCE_REVISION"
    if not source_file.is_file() or source_file.read_text(encoding="utf-8").strip() != revision:
        raise EvidenceError("built SOURCE_REVISION is missing or differs from checked-out source")
    if not tools.is_file():
        raise EvidenceError(f"tool inventory not found: {display_path(tools)}")
    inventory = tools.read_text(encoding="utf-8")
    if f"source-revision: {revision}\n" not in inventory:
        raise EvidenceError("tool inventory is stale or bound to a different source revision")
    environment = os.environ.copy()
    qemu = qemu_version(environment)
    accelerator = qemu_accelerator(environment)
    report = base_report(
        matrix, matrix_id, revision, source_file, tools, qemu, accelerator
    )
    write_report(output, report)

    jobs = args.jobs
    if jobs < 1:
        raise EvidenceError("jobs must be a positive integer")
    for row in rows:
        paths = expanded(row, version, build_dir)
        for kind in ("image", "elf"):
            if not paths[kind].is_file():
                raise EvidenceError(
                    f"scenario {row['id']} is missing {kind}: {display_path(paths[kind])}"
                )

    output.parent.mkdir(parents=True, exist_ok=True)
    worker_count = min(jobs, len(rows))
    print(
        f"evidence: running {len(rows)} scenarios with {worker_count} workers",
        flush=True,
    )
    with ThreadPoolExecutor(max_workers=worker_count) as executor:
        executions = {
            executor.submit(
                execute_scenario, row, build_dir, version, environment
            ): row
            for row in rows
        }
        completed_by_id = {}
        for execution in as_completed(executions):
            row = executions[execution]
            result = execution.result()
            completed_by_id[row["id"]] = result
            print(
                f"evidence: completed {row['id']} in {result[-1]:.2f}s",
                flush=True,
            )
        completed_scenarios = [completed_by_id[row["id"]] for row in rows]

    for row, execution in zip(rows, completed_scenarios, strict=True):
        (
            paths, command, scenario_environment, command_output, status, _duration,
        ) = execution
        command_log = output.parent / f"{row['id']}.command.log"
        command_log.write_text(command_output, encoding="utf-8")
        print(f"evidence: result {row['id']} ({row['result_class']})", flush=True)
        sys.stdout.write(command_output)
        if command_output and not command_output.endswith("\n"):
            sys.stdout.write("\n")
        sys.stdout.flush()

        result: dict[str, object] = {
            "id": row["id"],
            "expected_result_class": row["result_class"],
            "timeout_seconds": int(row["timeout"]),
            "runner": row["runner"],
            "runner_command": command,
            "runner_environment": scenario_environment,
            "runner_exit_status": status,
            "qemu_commands": re.findall(r"^QEMU command:(.*)$", command_output, re.MULTILINE),
            "artifacts": [
                {"kind": kind, "path": display_path(path), "sha256": sha256(path)}
                for kind, path in (("image", paths["image"]), ("elf", paths["elf"]))
            ],
            "command_log": {
                "path": display_path(command_log), "sha256": sha256(command_log)
            },
            "status": "FAIL",
        }
        if paths["serial_log"].is_file():
            result["serial_log"] = {
                "path": display_path(paths["serial_log"]),
                "sha256": sha256(paths["serial_log"]),
            }
        if row["runner"] in {"nmi", "multivcpu"} and paths[
            "qmp_transcript"
        ].is_file():
            result["qmp_transcript"] = {
                "path": display_path(paths["qmp_transcript"]),
                "sha256": sha256(paths["qmp_transcript"]),
            }
        report["results"].append(result)  # type: ignore[union-attr]
        # Keep a partial report machine-readable if any runner or subsequent
        # evidence check fails.  A fully validated scenario restores RUNNING;
        # only the complete selected matrix can publish PASS below.
        report["status"] = "FAIL"
        write_report(output, report)

        if status != 0:
            raise EvidenceError(
                f"scenario {row['id']} runner failed with exit status {status}"
            )
        if not paths["serial_log"].is_file() or paths["serial_log"].stat().st_size == 0:
            raise EvidenceError(f"scenario {row['id']} did not produce its expected serial log")
        verify_iotlb_oracle_rows(paths["serial_log"], row["id"])
        if "dma_snapshot" in paths and (
            not paths["dma_snapshot"].is_file()
            or paths["dma_snapshot"].stat().st_size == 0
        ):
            raise EvidenceError(
                f"scenario {row['id']} did not retain its DMA snapshot"
            )
        if "vtd_snapshot" in paths and (
            not paths["vtd_snapshot"].is_file()
            or paths["vtd_snapshot"].stat().st_size == 0
        ):
            raise EvidenceError(
                f"scenario {row['id']} did not retain its VT-d activation snapshot"
            )
        if row["runner"] in {"nmi", "multivcpu"} and (
            not paths["qmp_transcript"].is_file()
            or paths["qmp_transcript"].stat().st_size == 0
        ):
            raise EvidenceError(
                f"scenario {row['id']} did not retain its QMP transcript"
            )
        if row["runner"] == "multivcpu" and (
            not paths["multivcpu_inventory"].is_file()
            or paths["multivcpu_inventory"].stat().st_size == 0
        ):
            raise EvidenceError(
                f"scenario {row['id']} did not retain its normalized CPU inventory"
            )
        if len(result["qemu_commands"]) != 1:
            raise EvidenceError(
                f"scenario {row['id']} did not record exactly one QEMU command"
            )
        result["serial_log"] = {
            "path": display_path(paths["serial_log"]),
            "sha256": sha256(paths["serial_log"]),
        }
        if "dma_snapshot" in paths:
            result["artifacts"].append({
                "kind": "dma_snapshot",
                "path": display_path(paths["dma_snapshot"]),
                "sha256": sha256(paths["dma_snapshot"]),
            })
        if "vtd_snapshot" in paths:
            result["artifacts"].append({
                "kind": "vtd_snapshot",
                "path": display_path(paths["vtd_snapshot"]),
                "sha256": sha256(paths["vtd_snapshot"]),
            })
        if row["runner"] in {"nmi", "multivcpu"}:
            result["qmp_transcript"] = {
                "path": display_path(paths["qmp_transcript"]),
                "sha256": sha256(paths["qmp_transcript"]),
            }
        if row["runner"] == "multivcpu":
            result["artifacts"].append({
                "kind": "multivcpu_inventory",
                "path": display_path(paths["multivcpu_inventory"]),
                "sha256": sha256(paths["multivcpu_inventory"]),
            })
        result["status"] = "PASS"
        report["status"] = "RUNNING"
        write_report(output, report)

    report["status"] = "PASS"
    write_report(output, report)
    verify_report(
        output, matrix, build_dir, tools, version, environment,
        scenario=args.scenario,
        tier=args.tier,
        shard_index=args.shard_index,
        shard_count=args.shard_count,
    )
    print(f"emulator evidence matrix passed ({len(rows)} scenarios): {display_path(output)}")


def verify_hash(record: dict[str, object], label: str) -> None:
    path_value = record.get("path")
    expected = record.get("sha256")
    if not isinstance(path_value, str) or not isinstance(expected, str):
        raise EvidenceError(f"{label} lacks path or SHA-256")
    path = resolve_recorded(path_value)
    if not path.is_file():
        raise EvidenceError(f"{label} is missing: {path_value}")
    if sha256(path) != expected:
        raise EvidenceError(f"{label} hash differs: {path_value}")


def verify_iotlb_oracle_rows(path: Path, scenario_id: str) -> None:
    """Require the canonical QEMU boot to retain every bounded IOTLB row."""
    if scenario_id != "blocking-ipc":
        return
    serial = path.read_text(encoding="utf-8")
    for row in REQUIRED_IOTLB_ORACLE_ROWS:
        marker = f"LEANOS/3 ORACLE id={row} result=PASS"
        if serial.count(marker) != 1:
            raise EvidenceError(
                f"scenario {scenario_id} must retain exactly one passing {row} row"
            )


def verify_report(
    report_path: Path, matrix: Path, build_dir: Path, tools: Path,
    version: str, environment: dict[str, str], scenario: str | None = None,
    tier: str = "all",
    shard_index: int | None = None, shard_count: int | None = None,
) -> None:
    matrix_id, rows = parse_matrix(matrix)
    rows = select_rows(rows, scenario, tier, shard_index, shard_count)
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise EvidenceError(f"cannot read evidence report: {error}")
    if report.get("schema") != "leanos-emulator-evidence-report-v1":
        raise EvidenceError("evidence report has an unrecognized schema")
    if report.get("status") != "PASS":
        raise EvidenceError("evidence report is incomplete or failed")
    matrix_record = report.get("matrix")
    if not isinstance(matrix_record, dict) or matrix_record.get("id") != matrix_id:
        raise EvidenceError("evidence report matrix ID differs")
    if matrix_record.get("path") != display_path(matrix) or matrix_record.get("sha256") != sha256(matrix):
        raise EvidenceError("evidence report matrix identity differs")
    revision = git_revision()
    source = report.get("source")
    source_file = build_dir / "SOURCE_REVISION"
    if not isinstance(source, dict) or source.get("git_revision") != revision:
        raise EvidenceError("evidence report source revision differs")
    if not source_file.is_file() or source_file.read_text(encoding="utf-8").strip() != revision:
        raise EvidenceError("built SOURCE_REVISION differs during verification")
    if source.get("embedded_revision_path") != display_path(source_file) or source.get("embedded_revision_sha256") != sha256(source_file):
        raise EvidenceError("embedded source-revision identity differs")
    tool_record = report.get("tools")
    if not isinstance(tool_record, dict):
        raise EvidenceError("evidence report lacks tool identity")
    if tool_record.get("inventory_path") != display_path(tools) or tool_record.get("inventory_sha256") != sha256(tools):
        raise EvidenceError("tool inventory identity differs")
    if tool_record.get("inventory") != tools.read_text(encoding="utf-8").splitlines():
        raise EvidenceError("tool inventory content differs")
    if tool_record.get("qemu_version") != qemu_version(environment):
        raise EvidenceError("QEMU version differs from tested evidence")
    accelerator = qemu_accelerator(environment)
    execution = report.get("execution")
    if not isinstance(execution, dict) or execution != {
        "requested_accelerator": accelerator,
        "fallback_allowed": False,
    }:
        raise EvidenceError("QEMU accelerator contract differs")

    results = report.get("results")
    if not isinstance(results, list):
        raise EvidenceError("evidence report lacks scenario results")
    result_ids = [result.get("id") for result in results if isinstance(result, dict)]
    expected_ids = [row["id"] for row in rows]
    if result_ids != expected_ids:
        raise EvidenceError("evidence report has missing, duplicate, or reordered results")
    for row, result in zip(rows, results, strict=True):
        if not isinstance(result, dict) or result.get("status") != "PASS":
            raise EvidenceError(f"scenario {row['id']} is absent or did not pass")
        if result.get("expected_result_class") != row["result_class"]:
            raise EvidenceError(f"scenario {row['id']} result class differs")
        if result.get("runner") != row["runner"]:
            raise EvidenceError(f"scenario {row['id']} runner differs")
        if result.get("timeout_seconds") != int(row["timeout"]):
            raise EvidenceError(f"scenario {row['id']} timeout differs")
        if result.get("runner_exit_status") != 0:
            raise EvidenceError(f"scenario {row['id']} has a nonzero recorded result")
        paths = expanded(row, version, build_dir)
        expected_artifacts = {
            ("image", display_path(paths["image"])),
            ("elf", display_path(paths["elf"])),
        }
        if "dma_snapshot" in paths:
            expected_artifacts.add(
                ("dma_snapshot", display_path(paths["dma_snapshot"]))
            )
        if "vtd_snapshot" in paths:
            expected_artifacts.add(
                ("vtd_snapshot", display_path(paths["vtd_snapshot"]))
            )
        if "multivcpu_inventory" in paths:
            expected_artifacts.add(
                (
                    "multivcpu_inventory",
                    display_path(paths["multivcpu_inventory"]),
                )
            )
        artifacts = result.get("artifacts")
        if not isinstance(artifacts, list) or {
            (artifact.get("kind"), artifact.get("path"))
            for artifact in artifacts if isinstance(artifact, dict)
        } != expected_artifacts:
            raise EvidenceError(f"scenario {row['id']} artifact inventory differs")
        for artifact in artifacts:
            verify_hash(artifact, f"scenario {row['id']} artifact")
        serial = result.get("serial_log")
        if not isinstance(serial, dict) or serial.get("path") != display_path(paths["serial_log"]):
            raise EvidenceError(f"scenario {row['id']} serial-log identity differs")
        verify_hash(serial, f"scenario {row['id']} serial log")
        verify_iotlb_oracle_rows(paths["serial_log"], row["id"])
        if row["runner"] in {"nmi", "multivcpu"}:
            transcript = result.get("qmp_transcript")
            if (
                not isinstance(transcript, dict)
                or transcript.get("path") != display_path(paths["qmp_transcript"])
            ):
                raise EvidenceError(
                    f"scenario {row['id']} QMP-transcript identity differs"
                )
            verify_hash(transcript, f"scenario {row['id']} QMP transcript")
        command_log = result.get("command_log")
        if not isinstance(command_log, dict):
            raise EvidenceError(f"scenario {row['id']} command log is absent")
        verify_hash(command_log, f"scenario {row['id']} command log")
        commands = result.get("qemu_commands")
        if not isinstance(commands, list) or len(commands) != 1 or not commands[0]:
            raise EvidenceError(f"scenario {row['id']} exact QEMU command is absent")
        expected_command, expected_environment = scenario_invocation(
            row, paths, build_dir, version, accelerator
        )
        if result.get("runner_command") != expected_command:
            raise EvidenceError(f"scenario {row['id']} runner command differs")
        if result.get("runner_environment") != expected_environment:
            raise EvidenceError(f"scenario {row['id']} runner environment differs")


def bundle_relative_path(path_value: str | Path, root: Path) -> str:
    """Return one safe repository-relative path for the evidence archive."""
    path = Path(path_value)
    resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
    try:
        relative = resolved.relative_to(root.resolve())
    except ValueError as error:
        raise EvidenceError(f"bundle path escapes repository root: {path_value}") from error
    if not relative.parts:
        raise EvidenceError("bundle path cannot name the repository root")
    return relative.as_posix()


def bundle_report_inventory(
    report_path: Path, root: Path,
) -> tuple[set[str], dict[str, str], list[str]]:
    """Read report-bound paths and digests without hiding partial-run diagnostics."""
    required: set[str] = set()
    expected_hashes: dict[str, str] = {}
    errors: list[str] = []
    try:
        report_relative = bundle_relative_path(report_path, root)
    except EvidenceError as error:
        errors.append(str(error))
        return required, expected_hashes, errors
    required.add(report_relative)
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        errors.append(f"cannot read evidence report: {error}")
        return required, expected_hashes, errors
    if report.get("schema") != "leanos-emulator-evidence-report-v1":
        errors.append("evidence report has an unrecognized schema")
    if report.get("status") != "PASS":
        errors.append("evidence report is incomplete or failed")

    def add_record(path_value: object, digest_value: object, label: str) -> None:
        if not isinstance(path_value, str) or not isinstance(digest_value, str):
            errors.append(f"{label} lacks path or SHA-256")
            return
        try:
            relative = bundle_relative_path(path_value, root)
        except EvidenceError as error:
            errors.append(str(error))
            return
        if not re.fullmatch(r"[0-9a-f]{64}", digest_value):
            errors.append(f"{label} has an invalid SHA-256")
            return
        required.add(relative)
        previous = expected_hashes.setdefault(relative, digest_value)
        if previous != digest_value:
            errors.append(f"{label} records conflicting hashes for {relative}")

    def visit(value: object, label: str) -> None:
        if isinstance(value, dict):
            if "path" in value or "sha256" in value:
                add_record(value.get("path"), value.get("sha256"), label)
            for path_key, digest_key in (
                ("embedded_revision_path", "embedded_revision_sha256"),
                ("inventory_path", "inventory_sha256"),
            ):
                if path_key in value or digest_key in value:
                    add_record(value.get(path_key), value.get(digest_key), label)
            for key, child in value.items():
                visit(child, f"{label}.{key}")
        elif isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, f"{label}[{index}]")

    visit(report, "report")
    return required, expected_hashes, errors


def bundle_candidate(relative: str) -> bool:
    """Keep review evidence while excluding compiler and ISO staging intermediates."""
    path = Path(relative)
    if relative.startswith("build/boot/iso-"):
        return False
    if relative.startswith("build/ci/") and path.suffix == ".tar":
        return False
    if path.suffix in {".c", ".d", ".o"}:
        return False
    if path.name.endswith(("-prelink.elf", ".inputs.sha256")):
        return False
    return True


def write_bundle_member(archive: tarfile.TarFile, path: Path, relative: str) -> None:
    """Write a regular file with deterministic ownership and timestamp metadata."""
    stat = path.stat()
    info = tarfile.TarInfo(relative)
    info.size = stat.st_size
    info.mode = stat.st_mode & 0o777
    info.mtime = 0
    info.uid = 0
    info.gid = 0
    info.uname = "root"
    info.gname = "root"
    with path.open("rb") as source:
        archive.addfile(info, source)


def build_evidence_bundle(report_path: Path, output: Path, root: Path = ROOT) -> None:
    """Create one fail-closed, manifest-bound tarball for an emulator job."""
    root = root.resolve()
    output = output.resolve()
    try:
        output_relative = output.relative_to(root).as_posix()
    except ValueError as error:
        raise EvidenceError("bundle output must remain under the repository root") from error
    required, expected_hashes, validation_errors = bundle_report_inventory(
        report_path.resolve(), root
    )
    required.update(BUNDLE_REQUIRED_FILES)

    included: set[str] = set()
    for relative in BUNDLE_CONTEXT_FILES:
        path = root / relative
        if path.is_file() and not path.is_symlink():
            included.add(relative)
    for relative_root in BUNDLE_ROOTS:
        directory = root / relative_root
        if not directory.is_dir():
            continue
        for path in directory.rglob("*"):
            if not path.is_file() or path.is_symlink():
                continue
            relative = path.relative_to(root).as_posix()
            if relative != output_relative and bundle_candidate(relative):
                included.add(relative)
    for relative in required:
        path = root / relative
        if path.is_file() and not path.is_symlink() and relative != output_relative:
            included.add(relative)

    missing = sorted(relative for relative in required if relative not in included)
    records = []
    for relative in sorted(included):
        path = root / relative
        digest = sha256(path)
        expected = expected_hashes.get(relative)
        if expected is not None and digest != expected:
            validation_errors.append(f"report-bound hash differs: {relative}")
        records.append({
            "path": relative,
            "required": relative in required,
            "sha256": digest,
            "size": path.stat().st_size,
        })

    source_revision = None
    revision_path = root / "build/boot/SOURCE_REVISION"
    if revision_path.is_file():
        source_revision = revision_path.read_text(encoding="utf-8").strip()
    manifest = {
        "schema": "leanos-emulator-evidence-bundle-v1",
        "source_revision": source_revision,
        "report": bundle_relative_path(report_path, root),
        "required_files": sorted(required),
        "missing_required_files": missing,
        "validation_errors": sorted(set(validation_errors)),
        "files": records,
    }
    manifest_bytes = (
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")

    output.parent.mkdir(parents=True, exist_ok=True)
    temporary_handle = tempfile.NamedTemporaryFile(
        prefix=output.name + ".", suffix=".tmp", dir=output.parent, delete=False
    )
    temporary = Path(temporary_handle.name)
    temporary_handle.close()
    try:
        with tarfile.open(temporary, mode="w", format=tarfile.PAX_FORMAT) as archive:
            manifest_info = tarfile.TarInfo("MANIFEST.json")
            manifest_info.size = len(manifest_bytes)
            manifest_info.mode = 0o644
            manifest_info.mtime = 0
            manifest_info.uid = 0
            manifest_info.gid = 0
            manifest_info.uname = "root"
            manifest_info.gname = "root"
            archive.addfile(manifest_info, io.BytesIO(manifest_bytes))
            for relative in sorted(included):
                write_bundle_member(archive, root / relative, relative)
        temporary.replace(output)
    finally:
        temporary.unlink(missing_ok=True)

    failures = []
    if missing:
        failures.append("missing required files: " + ", ".join(missing))
    failures.extend(sorted(set(validation_errors)))
    if failures:
        raise EvidenceError(
            "evidence bundle is incomplete (diagnostic tar retained at "
            f"{bundle_relative_path(output, root)}): " + "; ".join(failures)
        )
    print(
        f"bundled emulator evidence ({len(records)} files): "
        f"{bundle_relative_path(output, root)}"
    )


def check_release_package(package: str) -> None:
    normalized = package.replace("\\\n", " ")
    commands = []
    for line in normalized.splitlines():
        try:
            commands.append(shlex.split(line, comments=True, posix=True))
        except ValueError as error:
            raise EvidenceError(f"package-release.sh cannot be parsed: {error}") from error
    copies = {
        (tokens[1], tokens[2])
        for tokens in commands
        if len(tokens) == 3 and tokens[0] == "cp"
    }
    checksum_tokens = next(
        (tokens for tokens in commands if "sha256sum" in tokens),
        None,
    )
    if checksum_tokens is None:
        raise EvidenceError("package-release.sh does not generate SHA256SUMS")
    for source, destination in REQUIRED_FAULT_RELEASE_ARTIFACTS:
        release_destination = f"$release/{destination}"
        if (source, release_destination) not in copies:
            raise EvidenceError(
                "package-release.sh does not copy mandatory fault evidence "
                f"{source} to {destination}"
            )
        if destination not in checksum_tokens:
            raise EvidenceError(
                "package-release.sh does not checksum mandatory fault evidence "
                f"{destination}"
            )


def check_workflows() -> None:
    parse_matrix(DEFAULT_MATRIX)
    workflow_contents: dict[str, str] = {}
    for relative in (".github/workflows/ci.yml", ".github/workflows/release.yml"):
        path = ROOT / relative
        content = path.read_text(encoding="utf-8")
        workflow_contents[relative] = content
        count = content.count("./scripts/run-emulator-evidence.py run")
        expected_count = 2 if relative == ".github/workflows/ci.yml" else 1
        if count != expected_count:
            raise EvidenceError(
                f"{relative} must invoke the shared emulator matrix exactly "
                f"{expected_count} time(s) (found {count})"
            )
        for bypass in (
            "./scripts/run-image.sh", "./scripts/run-return-corruptions.sh",
            "./scripts/run-double-fault.sh",
            "./scripts/run-entry-stack-overflow.sh",
            "./scripts/run-bootstrap32-ud.sh",
            "./scripts/run-bootstrap64-nmi.sh",
            "./scripts/run-malformed-handoff.sh",
        ):
            if bypass in content:
                raise EvidenceError(f"{relative} bypasses the shared emulator matrix with {bypass}")
    ci_content = workflow_contents[".github/workflows/ci.yml"]
    if "  merge_group:\n    branches:\n      - main\n" not in ci_content:
        raise EvidenceError(
            "CI must run complete evidence for merge-queue candidates targeting main"
        )
    promotion_condition = (
        "github.event_name != 'pull_request' || "
        "contains(github.event.pull_request.labels.*.name, 'ci:full-admission')"
    )
    if (
        "types: [opened, synchronize, reopened, labeled, unlabeled, ready_for_review]"
        not in ci_content
        or "LEANOS_CI_EVIDENCE_TIER: ${{ (" + promotion_condition
        + ") && 'all' || 'pr' }}" not in ci_content
    ):
        raise EvidenceError(
            "CI must promote only labeled pull requests to complete evidence"
        )
    hosted_job = re.search(
        r"(?ms)^  hosted-boundary:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:\n|\Z)",
        ci_content,
    )
    hosted_contract = (
        "if: github.event_name == 'pull_request' || github.event_name == 'merge_group'",
        "./scripts/check-hosted-generated-boundaries.sh ordinary",
        "./scripts/check-hosted-generated-boundaries.sh sanitized",
        "./scripts/check-hosted-sanitizer-negatives.sh",
        "if-no-files-found: error",
    )
    if hosted_job is None or any(
        token not in hosted_job.group("body") for token in hosted_contract
    ) or (
        "LEANOS_SKIP_HOSTED_BOUNDARY_REPLAY: "
        "${{ (github.event_name == 'pull_request' || github.event_name == "
        "'merge_group') && '1' || '0' }}"
        not in ci_content
    ):
        raise EvidenceError(
            "CI must parallelize complete hosted evidence for pull requests and merge groups"
        )
    ci_emulator = re.search(
        r"(?ms)^  emulator:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:\n|\Z)",
        ci_content,
    )
    if ci_emulator is None:
        raise EvidenceError("CI workflow does not define the emulator evidence job")
    for shard_contract in (
        "shard: [0, 1, 2, 3]",
        'LEANOS_EVIDENCE_TIER="${{ env.LEANOS_CI_EVIDENCE_TIER }}"',
        "LEANOS_EVIDENCE_SHARD_INDEX=\"${{ matrix.shard }}\"",
        "LEANOS_EVIDENCE_SHARD_COUNT=4",
        '--tier "${{ env.LEANOS_CI_EVIDENCE_TIER }}"',
        "--shard-index ${{ matrix.shard }}",
        "--shard-count 4",
        "emulator-shard-${{ matrix.shard }}.json",
        "leanos-boot-${{ github.sha }}-shard-${{ matrix.shard }}",
        "./scripts/run-emulator-evidence.py bundle",
        "--output build/ci/emulator-evidence-shard-${{ matrix.shard }}.tar",
        "path: build/ci/emulator-evidence-shard-${{ matrix.shard }}.tar",
        "if-no-files-found: error",
        "compression-level: 0",
    ):
        if shard_contract not in ci_emulator.group("body"):
            raise EvidenceError(
                "CI emulator evidence job does not preserve four-way shard contract: "
                + shard_contract
            )
    if "path: |" in ci_emulator.group("body"):
        raise EvidenceError(
            "CI emulator evidence job must upload one prebuilt tarball, not a YAML path list"
        )
    if ci_emulator.group("body").count("uses: actions/upload-artifact@") != 1:
        raise EvidenceError(
            "CI emulator evidence job must publish exactly one artifact per shard"
        )
    ci_emulator_timeout = re.search(
        r"(?m)^    timeout-minutes:\s*(\d+)\s*$",
        ci_emulator.group("body"),
    )
    if ci_emulator_timeout is None or int(ci_emulator_timeout.group(1)) < 60:
        raise EvidenceError(
            "CI emulator evidence job must allow at least 60 minutes for "
            "image, QEMU, reproducibility, and artifact checks"
        )
    for clang_evidence in (
        "./scripts/build-image.sh",
        "./scripts/write-reproducibility-manifest.sh",
        'LEANOS_EVIDENCE_TIER="${{ env.LEANOS_CI_EVIDENCE_TIER }}"',
        'LEANOS_EVIDENCE_SHARD_INDEX="${{ env.LEANOS_CI_EVIDENCE_TIER == '
        "'pr' && '0' || '' }}\"",
        'LEANOS_EVIDENCE_SHARD_COUNT="${{ env.LEANOS_CI_EVIDENCE_TIER == '
        "'pr' && '4' || '' }}\"",
        "--scenario blocking-ipc",
        "test -s build/boot/serial.log",
        "build/boot/serial.log",
        "build/evidence/clang-canonical.json",
    ):
        if clang_evidence not in ci_content:
            raise EvidenceError(
                "CI does not preserve tiered Clang canonical evidence: "
                + clang_evidence
            )
    if 'if [[ "${{ env.LEANOS_CI_EVIDENCE_TIER }}" == all ]]; then' not in ci_content:
        raise EvidenceError(
            "CI must create the canonical reproducibility manifest only for complete evidence"
        )
    independent_clang = re.search(
        r"(?ms)^  clang-reproducibility-build:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:\n|\Z)",
        ci_content,
    )
    if independent_clang is None or (
        "if: " + promotion_condition
        not in independent_clang.group("body")
    ):
        raise EvidenceError(
            "CI must run the independent Clang build for promoted complete evidence"
        )
    admission = re.search(
        r"(?ms)^  premerge-admission:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:\n|\Z)",
        ci_content,
    )
    admission_contract = (
        "name: Pre-merge full admission",
        "if: always() && github.event_name == 'pull_request'",
        "- repository-hygiene",
        "- lean",
        "- hosted-boundary",
        "- clang-image",
        "- clang-reproducibility-build",
        "- clang-reproducibility",
        "- emulator",
        "PROMOTED: ${{ contains(github.event.pull_request.labels.*.name, "
        "'ci:full-admission') }}",
        "CLANG_REPRO_COMPARE: ${{ needs.clang-reproducibility.result }}",
        "EMULATOR: ${{ needs.emulator.result }}",
        'if [[ "$PROMOTED" != true ]]; then',
        'if [[ "$result" != success ]]; then',
    )
    if admission is None or any(
        token not in admission.group("body") for token in admission_contract
    ):
        raise EvidenceError(
            "CI must fail closed on labeled complete pre-merge admission"
        )
    if "build/boot/clang-canonical.serial.log" in ci_content:
        raise EvidenceError(
            "CI names a Clang serial path outside the selected matrix scenario"
        )
    kvm_evidence = re.search(
        r"(?ms)^  kvm-evidence:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:\n|\Z)",
        ci_content,
    )
    kvm_contract = (
        "runs-on: ubuntu-24.04",
        "continue-on-error: true",
        "shard: [0, 1, 2, 3]",
        "python3 scripts/probe-kvm.py",
        "--device /dev/kvm",
        "--env LEANOS_QEMU_ACCELERATOR=kvm",
        "./scripts/run-emulator-evidence.py run",
        "--tier pr",
        "--shard-index ${{ matrix.shard }}",
        "--shard-count 4",
        "kvm-preflight-shard-${{ matrix.shard }}.json",
        '[[ "$status" == available ]] || exit 20',
        "kvm-evidence-shard-${{ matrix.shard }}.tar",
        "if-no-files-found: error",
    )
    if kvm_evidence is None or any(
        token not in kvm_evidence.group("body") for token in kvm_contract
    ) or "container:" in kvm_evidence.group("body"):
        raise EvidenceError(
            "CI KVM lane must remain explicit, four-way, artifact-backed, and non-blocking"
        )
    release_diagnostics = workflow_contents[".github/workflows/release.yml"]
    release_gate = re.search(
        r"(?ms)^  gate:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:\n|\Z)",
        release_diagnostics,
    )
    if release_gate is None:
        raise EvidenceError("release workflow does not define the gated evidence job")
    release_timeout = re.search(
        r"(?m)^    timeout-minutes:\s*(\d+)\s*$",
        release_gate.group("body"),
    )
    if release_timeout is None or int(release_timeout.group(1)) < 60:
        raise EvidenceError(
            "release evidence gate must allow at least 60 minutes for proof, "
            "reproducibility, image, and emulator checks"
        )
    for artifact in (
        "build/boot/*.map",
        "build/boot/*.disassembly.txt",
        "build/boot/*.qmp.jsonl",
        "build/boot/*.qmp.tsv",
        "build/boot/fault-containment-snapshot.txt",
        "build/boot/fault-readonly-write-snapshot.txt",
        "build/boot/fault-nx-execute-snapshot.txt",
        "build/boot/boot-page-plan*.h",
        "build/oracle/host-results.txt",
    ):
        if artifact not in release_diagnostics:
            raise EvidenceError(
                f"release diagnostics do not retain mandatory evidence pattern {artifact}"
            )
    package = (ROOT / "scripts/package-release.sh").read_text(encoding="utf-8")
    if "run-emulator-evidence.py verify" not in package:
        raise EvidenceError("package-release.sh does not verify shared emulator evidence")
    check_release_package(package)
    print("Emulator evidence matrix and workflow consistency checks passed")


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="operation", required=True)
    run_parser = subparsers.add_parser("run")
    verify_parser = subparsers.add_parser("verify")
    plan_parser = subparsers.add_parser("build-plan")
    bundle_parser = subparsers.add_parser("bundle")
    subparsers.add_parser("check")
    for subparser in (run_parser, verify_parser):
        subparser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
        subparser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD)
        subparser.add_argument("--tool-versions", type=Path, default=DEFAULT_TOOLS)
        subparser.add_argument("--version", default=os.environ.get("LEANOS_VERSION", "0.1.0"))
        subparser.add_argument(
            "--tier", choices=("all", "pr"), default="all",
            help="select the complete evidence inventory or the versioned PR subset",
        )
    plan_parser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
    plan_parser.add_argument(
        "--version", default=os.environ.get("LEANOS_VERSION", "0.1.0")
    )
    plan_parser.add_argument(
        "--tier", choices=("all", "pr"), default="all",
        help="select the complete evidence inventory or the versioned PR subset",
    )
    run_parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    run_parser.add_argument(
        "--jobs", type=int, default=max(1, os.cpu_count() or 1),
        help="maximum concurrent QEMU scenario processes (default: host CPU count)",
    )
    run_parser.add_argument(
        "--scenario",
        help="run one named scenario from the validated matrix",
    )
    for subparser in (run_parser, verify_parser, plan_parser):
        subparser.add_argument(
            "--shard-index", type=int,
            help="zero-based stable matrix shard to run or verify",
        )
        subparser.add_argument(
            "--shard-count", type=int,
            help="total stable matrix shards to run or verify",
        )
    verify_parser.add_argument("report", nargs="?", type=Path, default=DEFAULT_OUTPUT)
    bundle_parser.add_argument("report", nargs="?", type=Path, default=DEFAULT_OUTPUT)
    bundle_parser.add_argument("--output", type=Path, default=DEFAULT_BUNDLE)
    args = parser.parse_args()
    try:
        if args.operation == "run":
            run(args)
        elif args.operation == "verify":
            verify_report(
                args.report.resolve(), args.matrix.resolve(), args.build_dir.resolve(),
                args.tool_versions.resolve(), args.version, os.environ.copy(),
                tier=args.tier,
                shard_index=args.shard_index, shard_count=args.shard_count,
            )
            print(f"verified emulator evidence: {display_path(args.report)}")
        elif args.operation == "build-plan":
            print_build_plan(args)
        elif args.operation == "bundle":
            build_evidence_bundle(args.report, args.output)
        else:
            check_workflows()
    except EvidenceError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
