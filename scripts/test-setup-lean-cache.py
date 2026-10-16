#!/usr/bin/env python3
"""Fail-closed fixtures for the reusable Lean/Lake cache boundary."""

from copy import deepcopy
import importlib.util
from pathlib import Path
import tempfile

from workflow_yaml import load_workflow


ROOT = Path(__file__).resolve().parents[1]
ACTION = ROOT / ".github/actions/setup-lean/action.yml"
WORKFLOW = ROOT / ".github/workflows/ci.yml"

source = ACTION.read_text(encoding="utf-8")
lake_cache = source.split("    - name: Restore Lake build cache\n", maxsplit=1)[1]

expected_inputs = (
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "LeanOS.lean",
    "LeanOS/**/*.lean",
)
for expected in expected_inputs:
    if f"'{expected}'" not in lake_cache:
        raise AssertionError(f"Lake cache key omits immutable input {expected}")

if "lake-v2-${{ runner.os }}-${{ runner.arch }}-${{ hashFiles(" not in lake_cache:
    raise AssertionError("Lake cache key is not platform and input bound")
if "github.sha" in lake_cache:
    raise AssertionError("Lake cache is commit-bound instead of reusable by input digest")
if "restore-keys:" in lake_cache:
    raise AssertionError("Lake cache permits a partial stale-key fallback")

# CI Lake caches are bound to platform, CI image, and Lean inputs. The proofs
# part of the Lean lane keeps an exact-input cache, because the proof-time gate
# measures only the modules Lake rebuilds. Other lanes may fall back to the
# newest cache of the same platform and image (issue #574), but only when they
# prune outputs of deleted modules before any Lean command runs.
CACHE_ACTION = "actions/cache@cdf6c1fa76f9f475f3d7449005a359c84ca0f306"
KEY_PREFIX = "lake-ci-v1-${{ runner.os }}-${{ runner.arch }}-${{ env.LEANOS_CI_IMAGE_DIGEST }}-"
PRUNE = "python3 scripts/prune-lake-outputs.py"


def check_ci_caches(workflow: dict) -> None:
    jobs = workflow["jobs"]
    expected_jobs = {
        "lean", "hosted-boundary", "clang-hosted", "clang-image",
        "gcc-image-family", "emulator",
    }
    cache_jobs = {
        name for name, job in jobs.items()
        if any(str(step.get("uses", "")).startswith("actions/cache@")
               and step.get("with", {}).get("path") == ".lake"
               for step in job.get("steps", []))
    }
    if cache_jobs != expected_jobs:
        raise AssertionError(f"CI Lake cache jobs drifted: {sorted(cache_jobs)}")
    if "actions/cache" in str(jobs["clang-reproducibility-build"]):
        raise AssertionError("the independent reproducibility build must stay cold")
    exact_conditions = []
    for name in sorted(expected_jobs):
        steps = jobs[name]["steps"]
        caches = [index for index, step in enumerate(steps)
                  if step.get("with", {}).get("path") == ".lake"]
        for index in caches:
            step = steps[index]
            options = step["with"]
            if step["uses"].split()[0] != CACHE_ACTION:
                raise AssertionError(f"{name} CI Lake cache action is not digest pinned")
            key = options.get("key", "")
            if not key.startswith(KEY_PREFIX + "${{ hashFiles("):
                raise AssertionError(
                    f"{name} CI Lake cache is not bound to platform, container, and inputs"
                )
            for expected in expected_inputs:
                if f"'{expected}'" not in key:
                    raise AssertionError(
                        f"{name} CI Lake cache key omits immutable input {expected}"
                    )
            if "github.sha" in key:
                raise AssertionError(
                    f"{name} CI Lake cache is commit-bound instead of reusable by input digest"
                )
            fallback = options.get("restore-keys")
            if fallback is None:
                exact_conditions.append((name, step.get("if")))
                continue
            if fallback != KEY_PREFIX:
                raise AssertionError(f"{name} Lake cache falls back across platforms or images")
            if step.get("if") not in (None, "matrix.part != 'proofs'"):
                raise AssertionError(f"{name} Lake cache fallback has an unreviewed condition")
        prune = [index for index, step in enumerate(steps) if step.get("run") == PRUNE]
        if len(prune) != 1 or prune[0] != max(caches) + 1 or "if" in steps[prune[0]]:
            raise AssertionError(f"{name} must prune restored Lake outputs right after restore")
    if exact_conditions != [("lean", "matrix.part == 'proofs'")]:
        raise AssertionError(
            f"only the proofs part may and must use an exact-only cache: {exact_conditions}"
        )


workflow = load_workflow(WORKFLOW)
check_ci_caches(workflow)
for mutate in (
    lambda jobs: jobs["lean"]["steps"][2].update({"if": "matrix.part == 'images'"}),
    lambda jobs: jobs["lean"]["steps"][2]["with"].update({"restore-keys": KEY_PREFIX}),
    lambda jobs: jobs["hosted-boundary"]["steps"][1]["with"].update(
        {"restore-keys": "lake-ci-v1-"}),
    lambda jobs: jobs["emulator"]["steps"].pop(2),
    lambda jobs: jobs["clang-image"]["steps"][1]["with"].update(
        {"key": KEY_PREFIX + "${{ github.sha }}"}),
    lambda jobs: jobs["clang-reproducibility-build"]["steps"].insert(
        1, deepcopy(jobs["gcc-image-family"]["steps"][1])),
):
    mutated = deepcopy(workflow)
    mutate(mutated["jobs"])
    try:
        check_ci_caches(mutated)
    except AssertionError:
        continue
    raise AssertionError("unsafe CI Lake cache mutation accepted")

# Pruning removes every module output whose source is gone, and nothing else.
spec = importlib.util.spec_from_file_location(
    "prune_lake_outputs", ROOT / "scripts/prune-lake-outputs.py"
)
assert spec is not None and spec.loader is not None
prune_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prune_module)
with tempfile.TemporaryDirectory() as directory:
    repo = Path(directory)
    (repo / "LeanOS").mkdir()
    (repo / "LeanOS.lean").write_text("", encoding="utf-8")
    (repo / "LeanOS/Kept.lean").write_text("", encoding="utf-8")
    kept, gone = [], []
    for tree, suffixes in (
        ("lib/lean", (".olean", ".olean.hash", ".ilean", ".trace", ".setup.json")),
        ("ir", (".c", ".c.hash", ".c.o.export", ".c.o.export.trace")),
    ):
        base = repo / ".lake/build" / tree
        (base / "LeanOS/Deleted/Sub").mkdir(parents=True)
        for suffix in suffixes:
            for module, bucket in (("LeanOS", kept), ("LeanOS/Kept", kept),
                                   ("LeanOS/Deleted", gone),
                                   ("LeanOS/Deleted/Sub/Leaf", gone)):
                path = base / f"{module}{suffix}"
                path.write_text("", encoding="utf-8")
                bucket.append(path)
    binary = repo / ".lake/build/bin/leanos-oracle"
    binary.parent.mkdir(parents=True)
    binary.write_text("", encoding="utf-8")
    removed = prune_module.prune(repo)
    if sorted(removed) != sorted(gone) or any(path.exists() for path in gone):
        raise AssertionError("pruning did not remove exactly the outputs of deleted modules")
    if not all(path.exists() for path in kept) or not binary.exists():
        raise AssertionError("pruning removed an output that still has a source")
    if (repo / ".lake/build/lib/lean/LeanOS/Deleted").exists():
        raise AssertionError("pruning left an empty module directory")

print("Lean cache boundary fixtures passed")
