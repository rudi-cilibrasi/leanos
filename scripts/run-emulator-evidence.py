#!/usr/bin/env python3
"""Run and verify LeanOS's versioned, release-blocking QEMU evidence matrix."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MATRIX = ROOT / "scripts/emulator-evidence-matrix.tsv"
DEFAULT_BUILD = ROOT / "build/boot"
DEFAULT_OUTPUT = ROOT / "build/evidence/emulator-evidence.json"
DEFAULT_TOOLS = ROOT / "build/ci/tool-versions.txt"
RESULT_CLASSES = {"accepted-boot", "controlled-rejection", "fail-stop"}
RUNNERS = {"boot", "return", "double-fault", "double-fault-guard"}
RUNNER_RESULT_CLASSES = {
    "boot": "accepted-boot",
    "return": "controlled-rejection",
    "double-fault": "fail-stop",
    "double-fault-guard": "controlled-rejection",
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
        "serial_log", "scenario", "mode", "reason",
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
    if matrix_id != "leanos-emulator-evidence-v1":
        raise EvidenceError(f"unsupported matrix version: {matrix_id}")
    if len(rows) != mandatory_count:
        raise EvidenceError(
            f"mandatory inventory count differs: declared {mandatory_count}, found {len(rows)}"
        )

    serials = [row["serial_log"] for row in rows]
    if len(serials) != len(set(serials)):
        raise EvidenceError("matrix serial-log destinations are not unique")
    for key in ("image", "elf"):
        values = [row[key] for row in rows]
        if len(values) != len(set(values)):
            raise EvidenceError(f"matrix {key} artifacts are not unique")
    return matrix_id, rows


def expanded(row: dict[str, str], version: str, build_dir: Path) -> dict[str, Path]:
    return {
        key: build_dir / row[key].replace("@VERSION@", version)
        for key in ("image", "elf", "serial_log")
    }


def scenario_invocation(
    row: dict[str, str], paths: dict[str, Path], build_dir: Path, version: str
) -> tuple[list[str], dict[str, str]]:
    environment = {
        "LEANOS_VERSION": version,
        "LEANOS_QEMU_TIMEOUT_SECONDS": row["timeout"],
        "LEANOS_SERIAL_LOG": str(paths["serial_log"]),
    }
    if row["runner"] == "boot":
        environment["LEANOS_BOOT_SCENARIO"] = row["scenario"]
        command = ["./scripts/run-image.sh", str(paths["image"])]
    elif row["runner"] == "return":
        environment["LEANOS_BOOT_DIR"] = str(build_dir)
        environment["LEANOS_RETURN_CORRUPTION_FIXTURE"] = row["scenario"]
        command = ["./scripts/run-return-corruptions.sh"]
    elif row["runner"] == "double-fault":
        command = ["./scripts/run-double-fault.sh", str(paths["image"])]
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
    tools: Path, qemu: str,
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
        "results": [],
        "status": "RUNNING",
    }


def run(args: argparse.Namespace) -> None:
    matrix = args.matrix.resolve()
    build_dir = args.build_dir.resolve()
    output = args.output.resolve()
    tools = args.tool_versions.resolve()
    matrix_id, rows = parse_matrix(matrix)
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
    report = base_report(matrix, matrix_id, revision, source_file, tools, qemu)
    write_report(output, report)

    for row in rows:
        paths = expanded(row, version, build_dir)
        for kind in ("image", "elf"):
            if not paths[kind].is_file():
                raise EvidenceError(
                    f"scenario {row['id']} is missing {kind}: {display_path(paths[kind])}"
                )
        command, scenario_environment = scenario_invocation(
            row, paths, build_dir, version
        )
        combined_environment = environment.copy()
        combined_environment.update(scenario_environment)
        command_log = output.parent / f"{row['id']}.command.log"
        print(f"evidence: running {row['id']} ({row['result_class']})", flush=True)
        try:
            completed = subprocess.run(
                command, cwd=ROOT, env=combined_environment, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=int(row["timeout"]) + 5, check=False,
            )
            command_output = completed.stdout
            status = completed.returncode
        except subprocess.TimeoutExpired as error:
            command_output = (error.stdout or "")
            if isinstance(command_output, bytes):
                command_output = command_output.decode(errors="replace")
            command_output += "\nfailure_class=matrix-timeout: scenario runner exceeded outer limit\n"
            status = 124
        command_log.write_text(command_output, encoding="utf-8")
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
        report["results"].append(result)  # type: ignore[union-attr]
        write_report(output, report)

        if status != 0:
            raise EvidenceError(
                f"scenario {row['id']} runner failed with exit status {status}"
            )
        if not paths["serial_log"].is_file() or paths["serial_log"].stat().st_size == 0:
            raise EvidenceError(f"scenario {row['id']} did not produce its expected serial log")
        if len(result["qemu_commands"]) != 1:
            raise EvidenceError(
                f"scenario {row['id']} did not record exactly one QEMU command"
            )
        result["serial_log"] = {
            "path": display_path(paths["serial_log"]),
            "sha256": sha256(paths["serial_log"]),
        }
        result["status"] = "PASS"
        write_report(output, report)

    report["status"] = "PASS"
    write_report(output, report)
    verify_report(output, matrix, build_dir, tools, version, environment)
    print(f"emulator evidence matrix passed ({len(rows)} mandatory scenarios): {display_path(output)}")


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


def verify_report(
    report_path: Path, matrix: Path, build_dir: Path, tools: Path,
    version: str, environment: dict[str, str],
) -> None:
    matrix_id, rows = parse_matrix(matrix)
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
        command_log = result.get("command_log")
        if not isinstance(command_log, dict):
            raise EvidenceError(f"scenario {row['id']} command log is absent")
        verify_hash(command_log, f"scenario {row['id']} command log")
        commands = result.get("qemu_commands")
        if not isinstance(commands, list) or len(commands) != 1 or not commands[0]:
            raise EvidenceError(f"scenario {row['id']} exact QEMU command is absent")
        expected_command, expected_environment = scenario_invocation(
            row, paths, build_dir, version
        )
        if result.get("runner_command") != expected_command:
            raise EvidenceError(f"scenario {row['id']} runner command differs")
        if result.get("runner_environment") != expected_environment:
            raise EvidenceError(f"scenario {row['id']} runner environment differs")


def check_workflows() -> None:
    parse_matrix(DEFAULT_MATRIX)
    for relative in (".github/workflows/ci.yml", ".github/workflows/release.yml"):
        path = ROOT / relative
        content = path.read_text(encoding="utf-8")
        count = content.count("./scripts/run-emulator-evidence.py run")
        if count != 1:
            raise EvidenceError(
                f"{relative} must invoke the shared emulator matrix exactly once (found {count})"
            )
        for bypass in (
            "./scripts/run-image.sh", "./scripts/run-return-corruptions.sh",
            "./scripts/run-double-fault.sh",
        ):
            if bypass in content:
                raise EvidenceError(f"{relative} bypasses the shared emulator matrix with {bypass}")
    package = (ROOT / "scripts/package-release.sh").read_text(encoding="utf-8")
    if "run-emulator-evidence.py verify" not in package:
        raise EvidenceError("package-release.sh does not verify shared emulator evidence")
    print("Emulator evidence matrix and workflow consistency checks passed")


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="operation", required=True)
    run_parser = subparsers.add_parser("run")
    verify_parser = subparsers.add_parser("verify")
    subparsers.add_parser("check")
    for subparser in (run_parser, verify_parser):
        subparser.add_argument("--matrix", type=Path, default=DEFAULT_MATRIX)
        subparser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD)
        subparser.add_argument("--tool-versions", type=Path, default=DEFAULT_TOOLS)
        subparser.add_argument("--version", default=os.environ.get("LEANOS_VERSION", "0.1.0"))
    run_parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    verify_parser.add_argument("report", nargs="?", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    try:
        if args.operation == "run":
            run(args)
        elif args.operation == "verify":
            verify_report(
                args.report.resolve(), args.matrix.resolve(), args.build_dir.resolve(),
                args.tool_versions.resolve(), args.version, os.environ.copy(),
            )
            print(f"verified emulator evidence: {display_path(args.report)}")
        else:
            check_workflows()
    except EvidenceError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
