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
lean_job = workflow.split("  lean:\n", maxsplit=1)[1].split("\n  hosted-generated-boundary:", maxsplit=1)[0]
ci_cache = lean_job.split("      - name: Restore immutable Lake build cache\n", maxsplit=1)[1].split(
    "\n      - name: Build and check proofs", maxsplit=1
)[0]
for expected in expected_inputs:
    if f"'{expected}'" not in ci_cache:
        raise AssertionError(f"primary CI Lake cache key omits immutable input {expected}")

if "actions/cache@cdf6c1fa76f9f475f3d7449005a359c84ca0f306" not in ci_cache:
    raise AssertionError("primary CI Lake cache action is not digest pinned")
if "lake-ci-v1-${{ runner.os }}-${{ runner.arch }}-${{ env.LEANOS_CI_IMAGE_DIGEST }}-${{ hashFiles(" not in ci_cache:
    raise AssertionError("primary CI Lake cache is not bound to platform, container, and inputs")
if "github.sha" in ci_cache:
    raise AssertionError("primary CI Lake cache is commit-bound instead of reusable by input digest")
if "restore-keys:" in ci_cache:
    raise AssertionError("primary CI Lake cache permits a partial stale-key fallback")

print("Lean cache boundary fixtures passed")
