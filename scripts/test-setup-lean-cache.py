#!/usr/bin/env python3
"""Fail-closed fixtures for the reusable Lean/Lake cache boundary."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ACTION = ROOT / ".github/actions/setup-lean/action.yml"

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

print("Lean cache boundary fixtures passed")
