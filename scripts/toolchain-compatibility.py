#!/usr/bin/env python3
"""Run bounded compatibility evidence and compare its semantic contracts."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("profiles", ROOT / "scripts/toolchain-profile.py")
assert spec is not None and spec.loader is not None
profiles = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profiles)
evidence_spec = importlib.util.spec_from_file_location("emulator_evidence", ROOT / "scripts/run-emulator-evidence.py")
assert evidence_spec is not None and evidence_spec.loader is not None
emulator_evidence = importlib.util.module_from_spec(evidence_spec)
evidence_spec.loader.exec_module(emulator_evidence)
SCHEMA = "leanos-toolchain-compatibility-v1"
PHASES = ("environment", "proof-policy", "proofs", "proof-negative", "hosted", "image", "elf-negative",
          "protocol-negatives", "emulator", "verify")
SEMANTIC_FILES = {
    "oracle": "build/oracle/corpus.tsv",
    "hosted_results": "build/oracle/host-results.txt",
    "serial_vocabulary": "build/boot/serial-protocol.tsv",
    "elf_ownership_policy": "scripts/direct-port-sites.tsv",
}


def expected_scenarios() -> list[dict[str, Any]]:
    _, rows = emulator_evidence.parse_matrix(emulator_evidence.DEFAULT_MATRIX)
    return [{"id": r["id"], "result_class": r["result_class"], "status": "PASS",
             "runner_exit_status": 0}
            for r in emulator_evidence.select_rows(rows, None, "pr", 0, 4)]


def registry() -> tuple[dict[str, Any], dict[str, Any]]:
    data = profiles.load_json(profiles.DEFAULT_MANIFEST)
    return data, profiles.check_manifest(data, (ROOT / "lean-toolchain").read_text().strip())


def matrix() -> dict[str, Any]:
    _, entries = registry()
    return {"include": [
        {"profile": p["id"], "digest": p["reference_environment"]["ci_image_digest"],
         "image": "ghcr.io/rudi-cilibrasi/leanos-ci@" +
         p["reference_environment"]["ci_image_digest"]}
        for p in entries.values()
    ]}


def checked_output(command: list[str]) -> str:
    return subprocess.check_output(command, cwd=ROOT, text=True).strip()


def environment(profile: dict[str, Any], data: dict[str, Any]) -> None:
    """Reject identity drift before any proof or build evidence is produced."""
    if os.environ.get("LEANOS_CI_IMAGE_DIGEST") != profile["reference_environment"]["ci_image_digest"]:
        raise profiles.ProfileError("running container digest differs from selected profile")
    profiles.check_compiler(profile, profiles.compiler_version(profile["compiler"]["command"]))
    if checked_output(["uname", "-m"]) != "x86_64":
        raise profiles.ProfileError("compatibility evidence requires x86_64")
    inventory = dict(line.split("\t", 1) for line in checked_output(
        ["dpkg-query", "-W", "-f=${Package}\t${Version}\n"]
    ).splitlines())
    for pin in profile.get("apt_packages", data["canonical_apt_packages"]):
        name, version = pin.split("=", 1)
        if inventory.get(name) != version:
            raise profiles.ProfileError(f"installed package differs from profile: {pin}")
    expected_lean = profile["lean_toolchain"].split(":v", 1)[1]
    if re.match(rf"Lean \(version {re.escape(expected_lean)}(?:,|\s)", checked_output(["lean", "--version"])) is None:
        raise profiles.ProfileError("active Lean compiler differs from selected profile")


def write_report(path: Path, report: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


def semantic_contract(directory: Path) -> dict[str, str]:
    """Compare protocol contracts after their production validators pass.

    Binary hashes and addresses deliberately remain in the separate emulator
    report; they do not define cross-profile compatibility.
    """
    for name, path in SEMANTIC_FILES.items():
        if not (ROOT / path).is_file() or not (ROOT / path).stat().st_size:
            raise profiles.ProfileError(f"missing semantic evidence: {path}")
        shutil.copyfile(ROOT / path, directory / f"{name}.txt")
    return {name: profiles.sha256(directory / f"{name}.txt") for name in SEMANTIC_FILES}


def run(profile_id: str, output: Path) -> None:
    data, entries = registry()
    if profile_id not in entries:
        raise profiles.ProfileError(f"unknown toolchain profile: {profile_id}")
    profile = entries[profile_id]
    revision = checked_output(["git", "rev-parse", "HEAD"])
    report: dict[str, Any] = {
        "schema": SCHEMA, "profile": profile, "source_revision": revision,
        "registry_sha256": profiles.sha256(profiles.DEFAULT_MANIFEST),
        "started_at": datetime.now(timezone.utc).isoformat(),
        "status": "FAIL", "phases": [],
    }
    write_report(output, report)
    (ROOT / "build/compatibility").mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEANOS_TOOLCHAIN_PROFILE=profile_id,
               LEANOS_CC=profile["compiler"]["command"],
               LEANOS_HOST_CC=profile["compiler"]["command"],
               LEANOS_ELF_LAYOUT_PROFILE=profile["interfaces"]["direct_port_elf"],
               LEANOS_EVIDENCE_TIER="pr", LEANOS_EVIDENCE_SHARD_INDEX="0",
               LEANOS_EVIDENCE_SHARD_COUNT="4")
    evidence = "build/compatibility/emulator.json"
    tools = "build/compatibility/tool-versions.txt"
    commands = {
        "proof-policy": ["python3", "scripts/check-native-decide-policy.py"],
        # Enumerate the library explicitly so an unimported new module cannot
        # silently fall outside the compatibility proof claim.
        "proofs": ["lake", "build", "LeanOS"] + [
            path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
            for path in sorted((ROOT / "LeanOS").rglob("*.lean"))
        ],
        "proof-negative": ["bash", "-euc", "if lake env lean -DwarningAsError=true tests/negative/Sorry.lean > build/compatibility/proof-negative.log 2>&1; then exit 1; fi; grep -q 'sorry' build/compatibility/proof-negative.log"],
        "hosted": ["bash", "-euc", "lake build leanos-boot-plan leanos-vtd-plan; ./scripts/check-hosted-generated-boundaries.sh ordinary"],
        "image": ["bash", "scripts/build-image.sh"],
        "elf-negative": ["bash", "scripts/test-direct-port-sites.sh"],
        "protocol-negatives": ["bash", "scripts/test-run-image.sh"],
        "emulator": ["bash", "-euc", f"./scripts/record-tool-versions.sh {tools}; python3 scripts/run-emulator-evidence.py run --tier pr --shard-index 0 --shard-count 4 --tool-versions {tools} --output {evidence}"],
        "verify": ["python3", "scripts/run-emulator-evidence.py", "verify", evidence,
                   "--tier", "pr", "--shard-index", "0", "--shard-count", "4", "--tool-versions", tools],
    }
    try:
        for phase in PHASES:
            print(f"compatibility {profile_id}: {phase}", flush=True)
            if phase == "environment":
                environment(profile, data)
            else:
                log = output.parent / f"{phase}.log"
                with log.open("w") as stream:
                    result = subprocess.run(commands[phase], cwd=ROOT, env=env, stdout=stream,
                                            stderr=subprocess.STDOUT, check=False)
                if result.returncode:
                    print(log.read_text()[-12000:], file=sys.stderr)
                    raise profiles.ProfileError(f"{phase} failed with exit status {result.returncode}")
            report["phases"].append(phase)
            write_report(output, report)
        report["semantic"] = semantic_contract(output.parent)
        emulator = profiles.load_json(ROOT / evidence)
        report["scenarios"] = [
            {"id": r["id"], "result_class": r["expected_result_class"],
             "status": r["status"], "runner_exit_status": r["runner_exit_status"]}
            for r in emulator["results"]
        ]
        if report["scenarios"] != expected_scenarios():
            raise profiles.ProfileError("incomplete or failed emulator scenario inventory")
        report["status"] = "PASS"
    except (profiles.ProfileError, OSError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
        raise
    finally:
        # Keep raw guest transcripts alongside the phase and command logs,
        # including the failing transcript when the runner rejects one.
        try:
            logs = output.parent / "guest"
            for source in (ROOT / "build/boot").glob("*.log"):
                logs.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, logs / source.name)
        except OSError as error:
            report["status"] = "FAIL"
            report["error"] = f"cannot retain guest diagnostics: {error}"
            raise
        finally:
            report["completed_at"] = datetime.now(timezone.utc).isoformat()
            write_report(output, report)


def compare(reports: list[dict[str, Any]], revision: str) -> None:
    """Require a complete same-revision matrix; incomplete evidence is never green."""
    data, entries = registry()
    if any(not isinstance(r, dict) or not isinstance(r.get("profile"), dict)
           or not isinstance(r["profile"].get("id"), str) for r in reports):
        raise profiles.ProfileError("malformed compatibility report identity")
    ids = [r.get("profile", {}).get("id") for r in reports]
    if len(ids) != len(set(ids)) or set(ids) != set(entries):
        raise profiles.ProfileError("missing, duplicate, or unknown compatibility profiles")
    baseline = next(r for r in reports if r["profile"]["id"] == data["default_profile"])
    for report in reports:
        profile_id = report["profile"]["id"]
        if report.get("schema") != SCHEMA or report.get("status") != "PASS":
            raise profiles.ProfileError(f"{profile_id}: incomplete or failed evidence")
        if report["profile"] != entries[profile_id] or report.get("registry_sha256") != profiles.sha256(profiles.DEFAULT_MANIFEST):
            raise profiles.ProfileError(f"{profile_id}: stale profile identity")
        if report.get("phases") != list(PHASES):
            raise profiles.ProfileError(f"{profile_id}: missing evidence phase")
        if report.get("source_revision") != revision:
            raise profiles.ProfileError(f"{profile_id}: stale or different source revision")
        semantic = report.get("semantic", {})
        if not isinstance(semantic, dict) or set(semantic) != set(SEMANTIC_FILES) or any(
            not isinstance(v, str) or re.fullmatch(r"[0-9a-f]{64}", v) is None for v in semantic.values()
        ) or semantic != baseline.get("semantic"):
            raise profiles.ProfileError(f"{profile_id}: semantic contracts differ or are incomplete")
        scenarios = report.get("scenarios")
        if scenarios != expected_scenarios():
            raise profiles.ProfileError(f"{profile_id}: guest evidence differs or failed")


def read_report(path: Path) -> dict[str, Any]:
    report = profiles.load_json(path)
    if not isinstance(report, dict) or not isinstance(report.get("semantic"), dict):
        raise profiles.ProfileError(f"missing semantic evidence: {path}")
    for name in SEMANTIC_FILES:
        retained = path.parent / f"{name}.txt"
        if not retained.is_file() or not retained.stat().st_size or profiles.sha256(retained) != report["semantic"].get(name):
            raise profiles.ProfileError(f"missing or altered retained contract: {name}")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("matrix")
    runner = commands.add_parser("run")
    runner.add_argument("--profile", required=True)
    runner.add_argument("--output", type=Path, default=ROOT / "build/compatibility/report.json")
    comparison = commands.add_parser("compare")
    comparison.add_argument("reports", type=Path, nargs="+")
    args = parser.parse_args()
    try:
        if args.command == "matrix":
            print(json.dumps(matrix()))
        elif args.command == "run":
            run(args.profile, args.output)
        else:
            compare([read_report(path) for path in args.reports], checked_output(["git", "rev-parse", "HEAD"]))
            print("Compatibility contracts agree across the complete profile matrix")
        return 0
    except (profiles.ProfileError, OSError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
