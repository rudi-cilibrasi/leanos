#!/usr/bin/env python3
"""Fail-closed fixtures for the reusable Lean/Lake cache boundary."""

from pathlib import Path


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

workflow = WORKFLOW.read_text(encoding="utf-8")
job_boundaries = (
    ("lean", "hosted-boundary", "Build and check proofs"),
    ("hosted-boundary", "clang-image", "Replay hosted generated boundaries"),
    ("clang-image", "gcc-image-family", "Verify selected compiler propagation"),
    ("gcc-image-family", "clang-reproducibility-build", "Build canonical GCC image family"),
    ("emulator", "kvm-evidence", "Record tool versions"),
)
for job_name, next_job, next_step in job_boundaries:
    job = workflow.split(f"  {job_name}:\n", maxsplit=1)[1].split(
        f"\n  {next_job}:", maxsplit=1
    )[0]
    ci_cache = job.split(
        "      - name: Restore immutable Lake build cache\n", maxsplit=1
    )[1].split(f"\n      - name: {next_step}", maxsplit=1)[0]
    for expected in expected_inputs:
        if f"'{expected}'" not in ci_cache:
            raise AssertionError(
                f"{job_name} CI Lake cache key omits immutable input {expected}"
            )

    if "actions/cache@cdf6c1fa76f9f475f3d7449005a359c84ca0f306" not in ci_cache:
        raise AssertionError(f"{job_name} CI Lake cache action is not digest pinned")
    if "lake-ci-v1-${{ runner.os }}-${{ runner.arch }}-${{ env.LEANOS_CI_IMAGE_DIGEST }}-${{ hashFiles(" not in ci_cache:
        raise AssertionError(
            f"{job_name} CI Lake cache is not bound to platform, container, and inputs"
        )
    if "github.sha" in ci_cache:
        raise AssertionError(
            f"{job_name} CI Lake cache is commit-bound instead of reusable by input digest"
        )
    if "restore-keys:" in ci_cache:
        raise AssertionError(f"{job_name} CI Lake cache permits a partial stale-key fallback")

print("Lean cache boundary fixtures passed")
