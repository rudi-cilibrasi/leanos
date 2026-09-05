#!/usr/bin/env python3
"""Contract tests for independent reproducibility partition aggregation."""

from __future__ import annotations

import hashlib
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

    build_root = fixture / "build"
    build_root.mkdir()
    for artifact in ("a.elf", "m.map"):
        (build_root / artifact).write_text(artifact)
    emitted = json.loads(
        run(
            "result",
            plan_path,
            "--partition",
            0,
            "--build-root",
            build_root,
        ).stdout
    )
    if emitted["partition"] != 0 or sorted(emitted["artifacts"]) != ["a.elf", "m.map"]:
        raise AssertionError("partition result does not contain its exact artifact set")
    if emitted["planDigest"] != plan["planDigest"]:
        raise AssertionError("partition result is not bound to its plan")
    mismatched_manifest = dict(plan)
    mismatched_manifest["artifactManifestDigest"] = "f" * 64
    unsigned = dict(mismatched_manifest)
    unsigned.pop("planDigest")
    mismatched_manifest["planDigest"] = hashlib.sha256(
        json.dumps(unsigned, separators=(",", ":"), sort_keys=True).encode()
    ).hexdigest()
    mismatched_manifest_path = fixture / "mismatched-manifest-plan.json"
    mismatched_manifest_path.write_text(json.dumps(mismatched_manifest))
    reject(
        "result",
        mismatched_manifest_path,
        "--partition",
        0,
        "--build-root",
        build_root,
        diagnostic="artifact manifest digest mismatch",
    )
    reject(
        "result",
        plan_path,
        "--partition",
        1,
        "--build-root",
        build_root,
        diagnostic="partition artifact is missing",
    )
    reject(
        "result",
        plan_path,
        "--partition",
        9,
        "--build-root",
        build_root,
        diagnostic="unknown partition",
    )
    external = fixture / "external"
    external.write_text("not a partition artifact")
    (build_root / "m.map").unlink()
    (build_root / "m.map").symlink_to(external)
    reject(
        "result",
        plan_path,
        "--partition",
        0,
        "--build-root",
        build_root,
        diagnostic="partition artifact is a symlink",
    )
    (build_root / "m.map").unlink()
    (build_root / "m.map").write_text("m.map")

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
