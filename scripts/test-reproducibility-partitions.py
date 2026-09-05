#!/usr/bin/env python3
"""Contract tests for independent reproducibility partition aggregation."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/reproducibility-partitions.py"


def run(*arguments: object, check: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        ["python3", str(SCRIPT), *(str(argument) for argument in arguments)],
        text=True,
        capture_output=True,
    )
    if check and result.returncode:
        raise AssertionError(result.stderr)
    return result


def reject(*arguments: object, diagnostic: str) -> None:
    result = run(*arguments, check=False)
    if result.returncode == 0 or diagnostic not in result.stderr:
        raise AssertionError(f"expected {diagnostic!r}, got {result.stderr!r}")


with tempfile.TemporaryDirectory() as directory:
    fixture = Path(directory)
    artifacts = fixture / "artifacts.txt"
    artifacts.write_text("z.iso\na.elf\nm.map\nb.iso\n")
    revision = "a" * 40
    plan_path = fixture / "plan.json"
    plan_path.write_text(
        run(
            "plan",
            artifacts,
            "--partitions",
            2,
            "--source-revision",
            revision,
            "--toolchain-id",
            "clang-reference@18.1.3",
        ).stdout
    )
    plan = json.loads(plan_path.read_text())
    if plan["partitions"] != [
        {"id": 0, "artifacts": ["a.elf", "m.map"]},
        {"id": 1, "artifacts": ["b.iso", "z.iso"]},
    ]:
        raise AssertionError("partition plan is not deterministic")

    result_paths = []
    for partition in plan["partitions"]:
        result = {
            "partition": partition["id"],
            "sourceRevision": plan["sourceRevision"],
            "toolchainId": plan["toolchainId"],
            "artifactManifestDigest": plan["artifactManifestDigest"],
            "planDigest": plan["planDigest"],
            "artifacts": {path: str(partition["id"]) * 64 for path in partition["artifacts"]},
        }
        path = fixture / f"result-{partition['id']}.json"
        path.write_text(json.dumps(result))
        result_paths.append(path)

    aggregate = run("verify", plan_path, *result_paths).stdout.splitlines()
    if len(aggregate) != 4 or aggregate != sorted(aggregate, key=lambda line: line[66:]):
        raise AssertionError("aggregate manifest is incomplete or non-deterministic")

    reject("verify", plan_path, result_paths[0], diagnostic="missing partition results")
    reject(
        "verify",
        plan_path,
        result_paths[0],
        result_paths[0],
        diagnostic="duplicate partition result",
    )
    mismatched = json.loads(result_paths[1].read_text())
    mismatched["sourceRevision"] = "b" * 40
    result_paths[1].write_text(json.dumps(mismatched))
    reject(
        "verify",
        plan_path,
        *result_paths,
        diagnostic="sourceRevision mismatch",
    )

print("Reproducibility partition planning and aggregation fail closed")
