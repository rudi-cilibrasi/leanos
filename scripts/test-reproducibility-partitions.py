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

    verification = ("verify", plan_path, *result_paths, "--artifacts", artifacts)
    aggregate = run(*verification).stdout.splitlines()
    if [line[66:] for line in aggregate] != artifacts.read_text().splitlines():
        raise AssertionError("aggregate manifest does not preserve authoritative order")

    reject("verify", plan_path, result_paths[0], "--artifacts", artifacts,
           diagnostic="missing partition results")
    reject(
        "verify",
        plan_path,
        result_paths[0],
        result_paths[0],
        "--artifacts", artifacts,
        diagnostic="duplicate partition result",
    )
    mismatched = json.loads(result_paths[1].read_text())
    mismatched["sourceRevision"] = "b" * 40
    result_paths[1].write_text(json.dumps(mismatched))
    reject(
        "verify",
        plan_path,
        *result_paths,
        "--artifacts", artifacts,
        diagnostic="sourceRevision mismatch",
    )

    mismatched["sourceRevision"] = revision
    result_paths[1].write_text(json.dumps(mismatched))
    baseline_result = result_paths[1].read_text()

    # Match every emitted provenance field against the plan, and reject damaged
    # digests or an incomplete/extra artifact set independently of plan validity.
    for field in ("sourceRevision", "toolchainId", "artifactManifestDigest", "planDigest"):
        for value in (None, "wrong"):
            changed = json.loads(baseline_result)
            changed[field] = value
            result_paths[1].write_text(json.dumps(changed))
            reject(*verification, diagnostic=f"{field} mismatch")
    for value in (None, "", "g" * 64, "a" * 63):
        changed = json.loads(baseline_result)
        changed["artifacts"]["b.iso"] = value
        result_paths[1].write_text(json.dumps(changed))
        reject(*verification, diagnostic="invalid digest")
    for extra in (False, True):
        changed = json.loads(baseline_result)
        if extra:
            changed["artifacts"]["extra.iso"] = "a" * 64
        else:
            changed["artifacts"].pop("b.iso")
        result_paths[1].write_text(json.dumps(changed))
        reject(*verification, diagnostic="artifact set mismatch")
    changed = json.loads(baseline_result)
    changed["partition"] = True
    result_paths[1].write_text(json.dumps(changed))
    reject(*verification, diagnostic="unknown partition")
    result_paths[1].write_text(baseline_result)

    # A self-consistent plan digest is not a substitute for required metadata.
    def pin_plan(value):
        value.pop("planDigest", None)
        value["planDigest"] = hashlib.sha256(
            json.dumps(value, separators=(",", ":"), sort_keys=True).encode()
        ).hexdigest()
        plan_path.write_text(json.dumps(value))

    def reject_plan(value, diagnostic):
        pin_plan(value)
        reject("result", plan_path, "--partition", 0, "--build-root", build_root,
               diagnostic=diagnostic)
        reject(*verification, diagnostic=diagnostic)

    for field, diagnostic in (("sourceRevision", "invalid source revision"),
                              ("toolchainId", "invalid toolchain identity")):
        for value in (None, "", 1, "invalid value"):
            changed = json.loads(json.dumps(plan))
            changed[field] = value
            reject_plan(changed, diagnostic)
        changed = json.loads(json.dumps(plan))
        changed.pop(field)
        reject_plan(changed, diagnostic)
    for identifier in (True, 0, -1, 2, "1"):
        changed = json.loads(json.dumps(plan))
        changed["partitions"][1]["id"] = identifier
        diagnostic = "contiguous" if identifier == 2 else "invalid partition id"
        reject_plan(changed, diagnostic)
    for artifact in ("../escape", "/absolute", "a/../b", "./a.elf", "a//b",
                     "", "a\nb", "a\\b", "a\x00b", "a\tb", "a b"):
        changed = json.loads(json.dumps(plan))
        changed["partitions"][0]["artifacts"][0] = artifact
        reject_plan(changed, "invalid artifact path")

    pin_plan(json.loads(json.dumps(plan)))
    source = plan_path.read_text()
    plan_path.write_text(source.replace('"sourceRevision":', '"sourceRevision": null, "sourceRevision":', 1))
    reject(*verification, diagnostic="duplicate JSON key")
    plan_path.write_text(source)
    result_paths[1].write_text(baseline_result.replace('"b.iso":', '"b.iso": null, "b.iso":', 1))
    reject(*verification, diagnostic="duplicate JSON key")
    result_paths[1].write_text(baseline_result)

    # Dropping an artifact and recomputing both digests still cannot change the
    # revision-owned artifact inventory that the verifier is asked to consume.
    changed = json.loads(json.dumps(plan))
    changed["partitions"][0]["artifacts"].remove("a.elf")
    changed["artifactManifestDigest"] = hashlib.sha256(b"b.iso\nm.map\nz.iso\n").hexdigest()
    pin_plan(changed)
    reject(*verification, diagnostic="authoritative artifact list")
    pin_plan(json.loads(json.dumps(plan)))
    run(*verification)

print("Reproducibility partition planning and aggregation fail closed")
