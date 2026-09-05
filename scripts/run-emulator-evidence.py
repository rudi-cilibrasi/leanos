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

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from workflow_yaml import WorkflowYamlError, load_workflow


ROOT = SCRIPT_DIR.parent
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
    "scripts/toolchain-profiles.json",
)
BUNDLE_REQUIRED_FILES = (
    "build/boot/SHA256SUMS",
    "build/boot/SOURCE_REVISION",
    "build/boot/TOOLCHAIN_PROFILE.json",
    "build/ci/emulator-evidence.log",
    "build/ci/image-build.log",
    "build/ci/image-build-phases.tsv",
    "build/ci/tool-versions.txt",
    "build/evidence/q35-edu-dma.tsv",
    "build/evidence/q35-pci-construction.tsv",
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
class EvidenceError(RuntimeError):
    pass


DEFAULT_MANIFEST = ROOT / "scripts/scenario-manifest.json"
MANIFEST_SCHEMA = "leanos-scenario-manifest-v1"
ROW_TEMPLATE_KEYS = (
    "runner", "timeout", "image", "elf", "serial_log", "scenario", "mode", "reason",
)
ARTIFACT_PLACEHOLDERS = (
    "image", "elf", "elf_stem", "elf_suffix", "serial_log", "stem", "stem_dash", "scenario",
)
NEGATIVE_FAILURE_CLASSES = {"serial-protocol", "classified"}
IDENTIFIER = re.compile(r"^[a-z0-9][a-z0-9-]*$")


def load_manifest(path: Path = DEFAULT_MANIFEST) -> dict[str, object]:
    """Load and validate the per-scenario manifest: the one declarative source
    for what the matrix rows, artifact lists, and negative-evidence checks
    restated by hand before."""
    if not path.is_file():
        raise EvidenceError(f"scenario manifest not found: {display_path(path)}")
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise EvidenceError(f"scenario manifest is not valid JSON: {error}") from error
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise EvidenceError("scenario manifest has an unsupported schema")
    families = manifest.get("families")
    kinds = manifest.get("artifact_kinds")
    scenarios = manifest.get("scenarios")
    if not isinstance(families, dict) or not isinstance(kinds, dict) or not isinstance(scenarios, dict):
        raise EvidenceError("scenario manifest lacks families, artifact_kinds, or scenarios")
    for name, family in families.items():
        row = family.get("row") if isinstance(family, dict) else None
        if not IDENTIFIER.match(name) or not isinstance(row, dict):
            raise EvidenceError(f"scenario manifest family {name!r} is malformed")
        if set(row) != set(ROW_TEMPLATE_KEYS):
            raise EvidenceError(f"scenario manifest family {name!r} does not template every row field")
        if row["runner"] not in RUNNERS:
            raise EvidenceError(f"scenario manifest family {name!r} names an unknown runner")
    for name, kind in kinds.items():
        if not isinstance(kind, dict) or set(kind) != {"source", "release"}:
            raise EvidenceError(f"scenario manifest artifact kind {name!r} is malformed")
    for key in ("release_extras", "reproducibility_extras"):
        if not isinstance(manifest.get(key, []), list):
            raise EvidenceError(f"scenario manifest {key} must be a list")
    for scenario_id, entry in scenarios.items():
        if not IDENTIFIER.match(scenario_id) or not isinstance(entry, dict):
            raise EvidenceError(f"scenario manifest entry {scenario_id!r} is malformed")
        family = entry.get("family")
        if family is not None and family not in families:
            raise EvidenceError(
                f"scenario {scenario_id} names unknown family {family!r}"
            )
        for key in ("release_artifacts", "reproducibility_artifacts"):
            for kind in entry.get(key, ()):
                if kind not in kinds:
                    raise EvidenceError(
                        f"scenario {scenario_id} names unknown artifact kind {kind!r}"
                    )
        negative = entry.get("negative_evidence")
        if negative is not None:
            if (
                not isinstance(negative, dict)
                or set(negative) != {"directory", "count", "failure_class", "driver"}
                or not IDENTIFIER.match(str(negative["directory"]))
                or not isinstance(negative["count"], int)
                or negative["count"] < 1
                or negative["failure_class"] not in NEGATIVE_FAILURE_CLASSES
            ):
                raise EvidenceError(
                    f"scenario {scenario_id} declares malformed negative evidence"
                )
            if not (ROOT / str(negative["driver"])).is_file():
                raise EvidenceError(
                    f"scenario {scenario_id} negative-evidence driver is missing: "
                    f"{negative['driver']}"
                )
    return manifest


def fill_template(template: str, values: dict[str, str]) -> str:
    result = template
    while True:
        strip = re.search(r"\{id\|strip:([^}]*)\}", result)
        if strip is None:
            break
        prefix = strip.group(1)
        if not values["id"].startswith(prefix):
            raise EvidenceError(
                f"scenario {values['id']} does not carry the family prefix {prefix!r}"
            )
        result = result[: strip.start()] + values["id"][len(prefix):] + result[strip.end():]
    for key, value in values.items():
        result = result.replace("{" + key + "}", value)
    unresolved = re.search(r"\{[a-z_|:-]+\}", result)
    if unresolved is not None:
        raise EvidenceError(
            f"scenario {values.get('id', '?')} template placeholder is unresolved: "
            f"{unresolved.group(0)}"
        )
    return result


def derive_row(manifest: dict[str, object], scenario_id: str) -> dict[str, str] | None:
    """The matrix row a manifest scenario must have, or None when its family
    leaves the row free-form."""
    entry = manifest["scenarios"][scenario_id]
    family_name = entry.get("family")
    if family_name is None:
        return None
    template = manifest["families"][family_name]["row"]
    values = {"id": scenario_id}
    values.update(
        {key: value for key, value in entry.items() if isinstance(value, str) and key != "family"}
    )
    values["scenario"] = fill_template(template["scenario"], values)
    row = {key: fill_template(template[key], values) for key in ROW_TEMPLATE_KEYS}
    row["id"] = scenario_id
    row["result_class"] = RUNNER_RESULT_CLASSES[row["runner"]]
    return row


def check_manifest_rows(
    manifest: dict[str, object], rows_by_id: dict[str, dict[str, str]]
) -> None:
    for scenario_id, entry in manifest["scenarios"].items():
        row = rows_by_id.get(scenario_id)
        family = entry.get("family")
        if row is None:
            if family is None:
                raise EvidenceError(f"manifest scenario is absent from the matrix: {scenario_id}")
            raise EvidenceError(f"mandatory {family} scenario is absent: {scenario_id}")
        expected = derive_row(manifest, scenario_id)
        if expected is None:
            continue
        for key, value in expected.items():
            if row[key] != value:
                raise EvidenceError(
                    f"mandatory {family} scenario {scenario_id} has "
                    f"unexpected {key} {row[key]!r}"
                )
    for scenario_id in rows_by_id:
        if scenario_id not in manifest["scenarios"]:
            raise EvidenceError(
                f"matrix scenario has no manifest entry: {scenario_id}"
            )


def artifact_values(row: dict[str, str]) -> dict[str, str]:
    serial_log = row["serial_log"]
    if serial_log == "serial.log":
        stem = ""
    elif serial_log.endswith(".serial.log"):
        stem = serial_log[: -len(".serial.log")]
    else:
        raise EvidenceError(f"scenario {row['id']} serial log has no artifact stem")
    elf_stem = row["elf"][: -len(".elf")] if row["elf"].endswith(".elf") else row["elf"]
    return {
        "image": row["image"],
        "elf": row["elf"],
        "elf_stem": elf_stem,
        "elf_suffix": elf_stem[len("leanos"):],
        "serial_log": serial_log,
        "stem": stem,
        "stem_dash": f"-{stem}-" if stem else "-",
        "scenario": row["scenario"],
    }


def scenario_artifacts(
    manifest: dict[str, object], row: dict[str, str], kinds: list[str], version: str
) -> list[tuple[str, str]]:
    values = artifact_values(row)
    pairs = []
    for kind in kinds:
        spec = manifest["artifact_kinds"][kind]
        source = fill_template(spec["source"], values).replace("@VERSION@", version)
        release = fill_template(spec["release"], values).replace("@VERSION@", version)
        pairs.append((f"build/boot/{source}", release))
    return pairs


def release_artifacts(
    manifest: dict[str, object], rows: list[dict[str, str]], version: str
) -> list[tuple[str, str]]:
    """Every (source, release name) copied into a release, in matrix order,
    followed by the global extras."""
    rows_by_id = {row["id"]: row for row in rows}
    pairs = []
    for scenario_id, entry in manifest["scenarios"].items():
        kinds = entry.get("release_artifacts")
        if kinds:
            pairs.extend(scenario_artifacts(manifest, rows_by_id[scenario_id], kinds, version))
    for extra in manifest.get("release_extras", []):
        pairs.append(
            (f"build/boot/{extra['source']}", extra["release"].replace("@VERSION@", version))
        )
    destinations = [destination for _, destination in pairs]
    if len(destinations) != len(set(destinations)):
        raise EvidenceError("derived release artifacts have duplicate destinations")
    return pairs


def reproducibility_artifacts(
    manifest: dict[str, object], rows: list[dict[str, str]], version: str
) -> list[str]:
    """Every build/boot basename that must be byte-reproducible across
    independent runners, in matrix order, with the global extras after the
    canonical image."""
    rows_by_id = {row["id"]: row for row in rows}
    names: list[str] = []
    for scenario_id, entry in manifest["scenarios"].items():
        kinds = entry.get("reproducibility_artifacts")
        if not kinds:
            continue
        for source, _ in scenario_artifacts(manifest, rows_by_id[scenario_id], kinds, version):
            names.append(Path(source).name)
        if scenario_id == rows[0]["id"]:
            names.extend(manifest.get("reproducibility_extras", []))
    if len(names) != len(set(names)):
        raise EvidenceError("derived reproducibility artifacts are not unique")
    return names


def negative_evidence(manifest: dict[str, object]) -> dict[str, dict[str, object]]:
    return {
        scenario_id: entry["negative_evidence"]
        for scenario_id, entry in manifest["scenarios"].items()
        if "negative_evidence" in entry
    }


def check_artifacts_present(pairs: list[tuple[str, str]], root: Path) -> None:
    for source, _ in pairs:
        if not (root / source).is_file():
            raise EvidenceError(f"derived artifact is missing from the build: {source}")


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


def parse_matrix(
    path: Path, manifest_path: Path = DEFAULT_MANIFEST
) -> tuple[str, list[dict[str, str]]]:
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
    check_manifest_rows(load_manifest(manifest_path), rows_by_id)

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
    """Select one scenario or a deterministic duration-bound-weighted shard."""
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
    # Matrix timeouts are checked-in upper bounds for scenario duration. Use
    # them as deterministic fallback weights until representative measured
    # durations are promoted into the matrix. Longest-processing-time-first
    # assignment avoids the fixed-stride bias while stable source indexes and
    # shard indexes make ties reproducible.
    assignments: list[list[tuple[int, dict[str, str]]]] = [
        [] for _ in range(shard_count)
    ]
    assigned_weights = [0] * shard_count
    weighted_rows = sorted(
        enumerate(rows), key=lambda item: (-int(item[1]["timeout"]), item[0])
    )
    for source_index, row in weighted_rows:
        destination = min(
            range(shard_count), key=lambda index: (assigned_weights[index], index)
        )
        assignments[destination].append((source_index, row))
        assigned_weights[destination] += int(row["timeout"])
    selected = [
        row for _source_index, row in sorted(assignments[shard_index])
    ]
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


def serial_record(family: str, tag: str) -> str:
    """The exact guest line prefix of a versioned serial record, read from the
    generated vocabulary (LEANOS_SERIAL_PROTOCOL_TSV or the canonical build
    directory) so this runner never spells a record identity itself."""
    path = Path(
        os.environ.get("LEANOS_SERIAL_PROTOCOL_TSV", "build/boot/serial-protocol.tsv")
    )
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        if fields[0] == "record" and fields[1] == family and fields[2] == tag:
            return fields[4]
    raise EvidenceError(f"serial record {family}/{tag} is not in {path}")


def verify_iotlb_oracle_rows(path: Path, scenario_id: str) -> None:
    """Require the canonical QEMU boot to retain every bounded IOTLB row."""
    if scenario_id != "blocking-ipc":
        return
    serial = path.read_text(encoding="utf-8")
    for row in REQUIRED_IOTLB_ORACLE_ROWS:
        marker = f"{serial_record('3', 'ORACLE')} id={row} result=PASS"
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
    """The release packager must copy the derived artifact list and checksum
    its destinations; it may not restate a build/boot artifact by hand."""
    if "run-emulator-evidence.py release-artifacts" not in package:
        raise EvidenceError(
            "package-release.sh does not copy the derived release artifact list"
        )
    if re.search(r"^cp \"?build/boot/", package, re.M):
        raise EvidenceError(
            "package-release.sh restates a build/boot artifact instead of deriving it"
        )
    if "sha256sum" not in package or "release_destinations" not in package:
        raise EvidenceError(
            "package-release.sh does not checksum the derived release destinations"
        )


def workflow_step_runs(
    workflow: dict[str, object], relative: str
) -> list[tuple[str, str]]:
    """Return job-scoped run scripts from a structurally loaded workflow."""

    jobs = workflow.get("jobs")
    if not isinstance(jobs, dict):
        raise EvidenceError(f"{relative} must define a jobs mapping")
    runs: list[tuple[str, str]] = []
    for job_name, job in jobs.items():
        if not isinstance(job_name, str) or not isinstance(job, dict):
            raise EvidenceError(f"{relative} job {job_name!r} must be a mapping")
        steps = job.get("steps", [])
        if not isinstance(steps, list):
            raise EvidenceError(f"{relative} job {job_name!r} steps must be a sequence")
        for step_index, step in enumerate(steps):
            if not isinstance(step, dict):
                raise EvidenceError(
                    f"{relative} job {job_name!r} step {step_index} must be a mapping"
                )
            run = step.get("run")
            if run is not None and not isinstance(run, str):
                raise EvidenceError(
                    f"{relative} job {job_name!r} step {step_index} run must be a string"
                )
            if run is not None:
                runs.append((job_name, run))
    return runs


def workflow_job(
    workflow: dict[str, object], relative: str, job_name: str
) -> dict[str, object]:
    """Return one named workflow job with a job-local structural diagnostic."""

    jobs = workflow.get("jobs")
    if not isinstance(jobs, dict):
        raise EvidenceError(f"{relative} must define a jobs mapping")
    job = jobs.get(job_name)
    if not isinstance(job, dict):
        raise EvidenceError(f"{relative} must define job {job_name!r} as a mapping")
    return job


def workflow_job_steps(
    job: dict[str, object], relative: str, job_name: str
) -> list[dict[str, object]]:
    """Return structurally validated steps for one workflow job."""

    steps = job.get("steps", [])
    if not isinstance(steps, list) or any(
        not isinstance(step, dict) for step in steps
    ):
        raise EvidenceError(f"{relative} job {job_name!r} steps must be mappings")
    return steps


def check_workflows() -> None:
    parse_matrix(DEFAULT_MATRIX)
    workflows: dict[str, dict[str, object]] = {}
    for relative in (".github/workflows/ci.yml", ".github/workflows/release.yml"):
        path = ROOT / relative
        try:
            workflow = load_workflow(path)
        except WorkflowYamlError as error:
            raise EvidenceError(f"{relative} is not valid workflow YAML: {error}") from error
        workflows[relative] = workflow
        step_runs = workflow_step_runs(workflow, relative)
        count = sum(
            run.count("./scripts/run-emulator-evidence.py run") for _, run in step_runs
        )
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
            bypass_job = next((job for job, run in step_runs if bypass in run), None)
            if bypass_job is not None:
                raise EvidenceError(
                    f"{relative} job {bypass_job!r} bypasses the shared emulator "
                    f"matrix with {bypass}"
                )
    ci_workflow = workflows[".github/workflows/ci.yml"]
    ci_triggers = ci_workflow.get("on")
    merge_group = ci_triggers.get("merge_group") if isinstance(ci_triggers, dict) else None
    if not isinstance(merge_group, dict) or merge_group.get("branches") != ["main"]:
        raise EvidenceError(
            "CI must run complete evidence for merge-queue candidates targeting main"
        )
    promotion_condition = (
        "github.event_name != 'pull_request' || "
        "contains(github.event.pull_request.labels.*.name, 'ci:full-admission')"
    )
    pull_request = (
        ci_triggers.get("pull_request") if isinstance(ci_triggers, dict) else None
    )
    expected_pull_request_types = [
        "opened",
        "synchronize",
        "reopened",
        "labeled",
        "unlabeled",
        "ready_for_review",
    ]
    ci_env = ci_workflow.get("env")
    expected_evidence_tier = "${{ (" + promotion_condition + ") && 'all' || 'pr' }}"
    if (
        not isinstance(pull_request, dict)
        or pull_request.get("types") != expected_pull_request_types
        or not isinstance(ci_env, dict)
        or ci_env.get("LEANOS_CI_EVIDENCE_TIER") != expected_evidence_tier
    ):
        raise EvidenceError(
            "CI must promote only labeled pull requests to complete evidence"
        )
    hosted_job = workflow_job(
        ci_workflow, ".github/workflows/ci.yml", "hosted-boundary"
    )
    hosted_steps = workflow_job_steps(
        hosted_job, ".github/workflows/ci.yml", "hosted-boundary"
    )
    hosted_runs = [
        step.get("run")
        for step in hosted_steps
        if isinstance(step.get("run"), str)
    ]
    hosted_commands = (
        "./scripts/check-hosted-generated-boundaries.sh ordinary",
        "./scripts/check-hosted-generated-boundaries.sh sanitized",
        "./scripts/check-hosted-sanitizer-negatives.sh",
    )
    artifact_steps = [
        step
        for step in hosted_steps
        if isinstance(step.get("uses"), str)
        and step["uses"].startswith("actions/upload-artifact@")
    ]
    expected_skip = (
        "${{ (github.event_name == 'pull_request' || github.event_name == "
        "'merge_group') && '1' || '0' }}"
    )
    skip_is_structural = any(
        isinstance(step.get("env"), dict)
        and step["env"].get("LEANOS_SKIP_HOSTED_BOUNDARY_REPLAY") == expected_skip
        for job_name in ci_workflow.get("jobs", {})
        for step in workflow_job_steps(
            workflow_job(ci_workflow, ".github/workflows/ci.yml", job_name),
            ".github/workflows/ci.yml",
            job_name,
        )
    )
    if (
        hosted_job.get("if")
        != "github.event_name == 'pull_request' || github.event_name == 'merge_group'"
        or any(not any(command in run for run in hosted_runs) for command in hosted_commands)
        or not artifact_steps
        or any(
            not isinstance(step.get("with"), dict)
            or step["with"].get("if-no-files-found") != "error"
            for step in artifact_steps
        )
        or not skip_is_structural
    ):
        raise EvidenceError(
            "CI must parallelize complete hosted evidence for pull requests and merge groups"
        )
    ci_emulator = workflow_job(
        ci_workflow, ".github/workflows/ci.yml", "emulator"
    )
    emulator_strategy = ci_emulator.get("strategy")
    emulator_matrix = (
        emulator_strategy.get("matrix")
        if isinstance(emulator_strategy, dict)
        else None
    )
    if (
        not isinstance(emulator_matrix, dict)
        or emulator_matrix.get("shard") != [0, 1, 2, 3]
    ):
        raise EvidenceError(
            "CI job 'emulator' matrix.shard must be the four shards [0, 1, 2, 3]"
        )
    emulator_timeout = ci_emulator.get("timeout-minutes")
    if not isinstance(emulator_timeout, int) or emulator_timeout < 60:
        raise EvidenceError(
            "CI job 'emulator' timeout-minutes must allow at least 60 minutes "
            "for image, QEMU, reproducibility, and artifact checks"
        )
    emulator_steps = workflow_job_steps(
        ci_emulator, ".github/workflows/ci.yml", "emulator"
    )
    emulator_runs = [
        step["run"] for step in emulator_steps if isinstance(step.get("run"), str)
    ]
    emulator_commands = "\n".join(emulator_runs)
    for shard_contract in (
        'LEANOS_EVIDENCE_TIER="${{ env.LEANOS_CI_EVIDENCE_TIER }}"',
        "LEANOS_EVIDENCE_SHARD_INDEX=\"${{ matrix.shard }}\"",
        "LEANOS_EVIDENCE_SHARD_COUNT=4",
        '--tier "${{ env.LEANOS_CI_EVIDENCE_TIER }}"',
        "--shard-index ${{ matrix.shard }}",
        "--shard-count 4",
        "emulator-shard-${{ matrix.shard }}.json",
        "cp build/ci/image-family/gcc-image-build-phases.tsv "
        "build/ci/image-build-phases.tsv",
        "./scripts/run-emulator-evidence.py bundle",
        "--output build/ci/emulator-evidence-shard-${{ matrix.shard }}.tar",
    ):
        if shard_contract not in emulator_commands:
            raise EvidenceError(
                "CI job 'emulator' does not preserve its command contract: "
                + shard_contract
            )
    emulator_artifacts = [
        step
        for step in emulator_steps
        if isinstance(step.get("uses"), str)
        and step["uses"].startswith("actions/upload-artifact@")
    ]
    if len(emulator_artifacts) != 1:
        raise EvidenceError(
            "CI job 'emulator' must publish exactly one artifact per shard"
        )
    emulator_artifact_options = emulator_artifacts[0].get("with")
    expected_emulator_artifact = {
        "name": "leanos-boot-${{ github.sha }}-shard-${{ matrix.shard }}",
        "path": "build/ci/emulator-evidence-shard-${{ matrix.shard }}.tar",
        "if-no-files-found": "error",
        "compression-level": 0,
    }
    if not isinstance(emulator_artifact_options, dict) or any(
        emulator_artifact_options.get(key) != value
        for key, value in expected_emulator_artifact.items()
    ):
        raise EvidenceError(
            "CI job 'emulator' upload-artifact step must publish the single "
            "prebuilt shard tarball with fail-closed, uncompressed options"
        )
    clang_image = workflow_job(
        ci_workflow, ".github/workflows/ci.yml", "clang-image"
    )
    clang_steps = workflow_job_steps(
        clang_image, ".github/workflows/ci.yml", "clang-image"
    )
    clang_commands = "\n".join(
        step["run"] for step in clang_steps if isinstance(step.get("run"), str)
    )
    clang_artifacts = [
        step
        for step in clang_steps
        if isinstance(step.get("uses"), str)
        and step["uses"].startswith("actions/upload-artifact@")
    ]
    clang_artifact_paths = "\n".join(
        str(options.get("path", ""))
        for step in clang_artifacts
        for options in [step.get("with")]
        if isinstance(options, dict)
    )
    for clang_command in (
        "./scripts/build-image.sh",
        "./scripts/write-reproducibility-manifest.sh",
        'LEANOS_EVIDENCE_TIER="${{ env.LEANOS_CI_EVIDENCE_TIER }}"',
        'LEANOS_EVIDENCE_SHARD_INDEX="${{ env.LEANOS_CI_EVIDENCE_TIER == '
        "'pr' && '0' || '' }}\"",
        'LEANOS_EVIDENCE_SHARD_COUNT="${{ env.LEANOS_CI_EVIDENCE_TIER == '
        "'pr' && '4' || '' }}\"",
        "--scenario blocking-ipc",
        "test -s build/boot/serial.log",
    ):
        if clang_command not in clang_commands:
            raise EvidenceError(
                "CI job 'clang-image' does not preserve its command contract: "
                + clang_command
            )
    for clang_artifact in (
        "build/boot/serial.log",
        "build/evidence/clang-canonical.json",
    ):
        if clang_artifact not in clang_artifact_paths:
            raise EvidenceError(
                "CI job 'clang-image' does not retain canonical artifact: "
                + clang_artifact
            )
    if 'if [[ "${{ env.LEANOS_CI_EVIDENCE_TIER }}" == all ]]; then' not in clang_commands:
        raise EvidenceError(
            "CI job 'clang-image' must create the canonical reproducibility "
            "manifest only for complete evidence"
        )
    independent_clang = workflow_job(
        ci_workflow, ".github/workflows/ci.yml", "clang-reproducibility-build"
    )
    if independent_clang.get("if") != promotion_condition:
        raise EvidenceError(
            "CI job 'clang-reproducibility-build' must run only for promoted "
            "complete evidence"
        )
    admission = workflow_job(
        ci_workflow, ".github/workflows/ci.yml", "premerge-admission"
    )
    admission_steps = workflow_job_steps(
        admission, ".github/workflows/ci.yml", "premerge-admission"
    )
    admission_runs = "\n".join(
        step["run"] for step in admission_steps if isinstance(step.get("run"), str)
    )
    expected_admission_needs = [
        "repository-hygiene",
        "lean",
        "hosted-boundary",
        "clang-image",
        "gcc-image-family",
        "clang-reproducibility-build",
        "clang-reproducibility",
        "emulator",
    ]
    expected_admission_env = {
        "PROMOTED": "${{ contains(github.event.pull_request.labels.*.name, "
        "'ci:full-admission') }}",
        "GCC_IMAGE_FAMILY": "${{ needs.gcc-image-family.result }}",
        "CLANG_REPRO_COMPARE": "${{ needs.clang-reproducibility.result }}",
        "EMULATOR": "${{ needs.emulator.result }}",
    }
    admission_step = next(
        (step for step in admission_steps if isinstance(step.get("run"), str)), None
    )
    admission_env = admission_step.get("env") if admission_step is not None else None
    if (
        admission.get("name") != "Pre-merge full admission"
        or admission.get("if") != "always() && github.event_name == 'pull_request'"
        or admission.get("needs") != expected_admission_needs
        or not isinstance(admission_env, dict)
        or any(
            admission_env.get(key) != value
            for key, value in expected_admission_env.items()
        )
        or 'if [[ "$PROMOTED" != true ]]; then' not in admission_runs
        or 'if [[ "$result" != success ]]; then' not in admission_runs
    ):
        raise EvidenceError(
            "CI job 'premerge-admission' must fail closed on labeled complete "
            "pre-merge admission with the full dependency and result contract"
        )
    if "build/boot/clang-canonical.serial.log" in (
        clang_commands + "\n" + clang_artifact_paths
    ):
        raise EvidenceError(
            "CI names a Clang serial path outside the selected matrix scenario"
        )
    kvm_evidence = workflow_job(
        ci_workflow, ".github/workflows/ci.yml", "kvm-evidence"
    )
    kvm_strategy = kvm_evidence.get("strategy")
    kvm_matrix = (
        kvm_strategy.get("matrix") if isinstance(kvm_strategy, dict) else None
    )
    kvm_steps = workflow_job_steps(
        kvm_evidence, ".github/workflows/ci.yml", "kvm-evidence"
    )
    kvm_commands = "\n".join(
        step["run"] for step in kvm_steps if isinstance(step.get("run"), str)
    )
    kvm_contract = (
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
    )
    kvm_artifacts = [
        step
        for step in kvm_steps
        if isinstance(step.get("uses"), str)
        and step["uses"].startswith("actions/upload-artifact@")
    ]
    kvm_artifact_options = (
        kvm_artifacts[0].get("with") if len(kvm_artifacts) == 1 else None
    )
    if (
        kvm_evidence.get("runs-on") != "ubuntu-24.04"
        or kvm_evidence.get("continue-on-error") is not True
        or "container" in kvm_evidence
        or not isinstance(kvm_matrix, dict)
        or kvm_matrix.get("shard") != [0, 1, 2, 3]
        or any(token not in kvm_commands for token in kvm_contract)
        or not isinstance(kvm_artifact_options, dict)
        or kvm_artifact_options.get("if-no-files-found") != "error"
    ):
        raise EvidenceError(
            "CI KVM lane must remain explicit, four-way, artifact-backed, and non-blocking"
        )
    release_workflow = workflows[".github/workflows/release.yml"]
    release_gate = workflow_job(
        release_workflow, ".github/workflows/release.yml", "gate"
    )
    release_timeout = release_gate.get("timeout-minutes")
    if not isinstance(release_timeout, int) or release_timeout < 60:
        raise EvidenceError(
            "release evidence gate must allow at least 60 minutes for proof, "
            "reproducibility, image, and emulator checks"
        )
    release_steps = workflow_job_steps(
        release_gate, ".github/workflows/release.yml", "gate"
    )
    release_artifacts = [
        step
        for step in release_steps
        if isinstance(step.get("uses"), str)
        and step["uses"].startswith("actions/upload-artifact@")
    ]
    release_paths = "\n".join(
        str(options.get("path", ""))
        for step in release_artifacts
        for options in [step.get("with")]
        if isinstance(options, dict)
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
        if artifact not in release_paths:
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
    release_parser = subparsers.add_parser("release-artifacts")
    reproducibility_parser = subparsers.add_parser("reproducibility-artifacts")
    negative_parser = subparsers.add_parser("negative-evidence")
    negative_parser.add_argument("scenario", nargs="?")
    for subparser in (release_parser, reproducibility_parser):
        subparser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
        subparser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
        subparser.add_argument("--version", default=os.environ.get("LEANOS_VERSION", "0.1.0"))
        subparser.add_argument(
            "--check", action="store_true",
            help="require every derived source to exist under the repository build",
        )
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
        elif args.operation == "release-artifacts":
            manifest = load_manifest(args.manifest)
            _, rows = parse_matrix(args.matrix, args.manifest)
            pairs = release_artifacts(manifest, rows, args.version)
            if args.check:
                check_artifacts_present(pairs, ROOT)
            for source, destination in pairs:
                print(f"{source}\t{destination}")
        elif args.operation == "reproducibility-artifacts":
            manifest = load_manifest(args.manifest)
            _, rows = parse_matrix(args.matrix, args.manifest)
            names = reproducibility_artifacts(manifest, rows, args.version)
            if args.check:
                check_artifacts_present([(f"build/boot/{name}", name) for name in names], ROOT)
            for name in names:
                print(name)
        elif args.operation == "negative-evidence":
            declared = negative_evidence(load_manifest())
            if args.scenario is not None:
                if args.scenario not in declared:
                    raise EvidenceError(
                        f"scenario {args.scenario} declares no negative evidence"
                    )
                declared = {args.scenario: declared[args.scenario]}
            for scenario_id, entry in declared.items():
                print(
                    f"{scenario_id}\t{entry['directory']}\t{entry['count']}\t"
                    f"{entry['failure_class']}\t{entry['driver']}"
                )
        else:
            check_workflows()
    except EvidenceError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
