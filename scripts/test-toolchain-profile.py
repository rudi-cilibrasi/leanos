#!/usr/bin/env python3
"""Controlled-negative fixtures for toolchain profile resolution."""

from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "toolchain-profile.py"
SPEC = importlib.util.spec_from_file_location("toolchain_profile", CHECKER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {CHECKER}")
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


def expect_failure(data: Any, needle: str) -> None:
    try:
        checker.check_manifest(data, "leanprover/lean4:v4.32.0")
    except checker.ProfileError as error:
        if needle not in str(error):
            raise AssertionError(f"missing expected diagnostic {needle!r}: {error}") from error
    else:
        raise AssertionError(f"profile mutation unexpectedly passed: {needle}")


def expect_compiler_failure(profile: dict[str, Any], version: str) -> None:
    try:
        checker.check_compiler(profile, version)
    except checker.ProfileError:
        return
    raise AssertionError(f"compiler mismatch unexpectedly passed: {version}")


def main() -> None:
    manifest = checker.load_json(checker.DEFAULT_MANIFEST)
    profiles = checker.check_manifest(manifest, "leanprover/lean4:v4.32.0")
    gcc = profiles["gcc-reference"]
    clang = profiles["clang-reference"]
    checker.check_compiler(gcc, "gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0")
    checker.check_compiler(clang, "Ubuntu clang version 18.1.3 (1ubuntu1)")
    expect_compiler_failure(gcc, "Ubuntu clang version 18.1.3 (1ubuntu1)")
    expect_compiler_failure(gcc, "gcc (Ubuntu 13.2.0) 13.2.0")
    expect_compiler_failure(clang, "Ubuntu clang version 19.1.1")

    duplicate = copy.deepcopy(manifest)
    duplicate["profiles"][1]["id"] = "gcc-reference"
    expect_failure(duplicate, "duplicate or malformed")

    floating = copy.deepcopy(manifest)
    floating["profiles"][1]["reference_environment"]["ci_image_digest"] = "latest"
    expect_failure(floating, "floating CI image")

    second_canonical = copy.deepcopy(manifest)
    second_canonical["profiles"][1]["status"] = "canonical"
    second_canonical["profiles"][1]["claim"] = "byte-reproducible-reference"
    expect_failure(second_canonical, "single canonical profile")

    unknown_layout = copy.deepcopy(manifest)
    unknown_layout["profiles"][1]["interfaces"]["direct_port_elf"] = "automatic"
    expect_failure(unknown_layout, "unknown ELF normalization")

    wrong_lean = copy.deepcopy(manifest)
    wrong_lean["profiles"][0]["lean_toolchain"] = "leanprover/lean4:v4.33.0"
    expect_failure(wrong_lean, "differs from lean-toolchain")

    floating_compiler = copy.deepcopy(manifest)
    floating_compiler["profiles"][1]["compiler"]["version"] = "18"
    expect_failure(floating_compiler, "invalid compiler version")

    duplicate_package = copy.deepcopy(manifest)
    duplicate_package["canonical_apt_packages"].append(
        duplicate_package["canonical_apt_packages"][0]
    )
    expect_failure(duplicate_package, "unique exact package pins")

    duplicate_package_name = copy.deepcopy(manifest)
    duplicate_package_name["canonical_apt_packages"].append("binutils=0")
    expect_failure(duplicate_package_name, "unique package names")

    floating_package = copy.deepcopy(manifest)
    floating_package["canonical_apt_packages"][0] = "binutils=*"
    expect_failure(floating_package, "unique exact package pins")

    unsafe_package = copy.deepcopy(manifest)
    unsafe_package["canonical_apt_packages"][1] = (
        "ca-certificates=20260601~24.04.1;true"
    )
    expect_failure(unsafe_package, "unique exact package pins")

    compiler_package_drift = copy.deepcopy(manifest)
    compiler_package_drift["profiles"][0]["compiler"]["package"] = (
        "gcc=4:13.2.0-7ubuntu0 (GCC 13.3.0)"
    )
    expect_failure(compiler_package_drift, "compiler package differs")

    shared_package_drift = copy.deepcopy(manifest)
    shared_package_drift["profiles"][1]["shared_tools"]["binutils"] = (
        "binutils=2.42-4ubuntu2.9"
    )
    expect_failure(shared_package_drift, "shared tool binutils differs")

    malformed_shared_package = copy.deepcopy(manifest)
    malformed_shared_package["profiles"][0]["shared_tools"]["binutils"] = (
        "binutils 2.42-4ubuntu2.10"
    )
    expect_failure(malformed_shared_package, "must use exact apt package pins")

    selection = checker.artifact(
        checker.DEFAULT_MANIFEST,
        gcc,
        "gcc",
        "gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0",
    )
    if selection["profile"]["claim"] != "byte-reproducible-reference":
        raise AssertionError("canonical selection lost its reproducibility claim")
    if len(selection["manifest"]["sha256"]) != 64:
        raise AssertionError("profile selection omitted the manifest identity")
    json.dumps(selection, sort_keys=True)

    ci = (ROOT / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    if "LEANOS_TOOLCHAIN_PROFILE: gcc-reference" not in ci:
        raise AssertionError("CI lost its canonical default toolchain profile")
    if ci.count("LEANOS_TOOLCHAIN_PROFILE: clang-reference") != 3:
        raise AssertionError("CI does not bind every Clang image lane to its profile")
    digest = gcc["reference_environment"]["ci_image_digest"]
    if ci.count(f"leanos-ci@{digest}") < 5:
        raise AssertionError("CI profile digest differs from the admitted build image")
    for relative in (
        ".github/workflows/release.yml",
        ".github/workflows/pages.yml",
        ".github/workflows/ci-image.yml",
    ):
        content = (ROOT / relative).read_text(encoding="utf-8")
        if "LEANOS_TOOLCHAIN_PROFILE: gcc-reference" not in content:
            raise AssertionError(f"{relative} lost the canonical toolchain profile")
    ci_image = (ROOT / ".github" / "workflows" / "ci-image.yml").read_text(
        encoding="utf-8"
    )
    for contract in (
        "\nenv:\n  LEANOS_TOOLCHAIN_PROFILE: gcc-reference\n\njobs:\n",
        "\n  publish:\n",
        "\n    permissions:\n      contents: read\n      packages: write\n    steps:\n",
        "            --env LEANOS_TOOLCHAIN_PROFILE \\\n",
    ):
        if contract not in ci_image:
            raise AssertionError("CI image workflow lost its job/profile hierarchy")

    build = (ROOT / "scripts" / "build-image.sh").read_text(encoding="utf-8")
    for contract in (
        "./scripts/toolchain-profile.py resolve",
        '--output "$build/TOOLCHAIN_PROFILE.json"',
        '--layout-profile "$layout_profile"',
        '"$staging_root/boot/TOOLCHAIN_PROFILE.json"',
    ):
        if contract not in build:
            raise AssertionError(f"image build lost toolchain profile contract: {contract}")

    reproducibility = (
        ROOT / "scripts" / "write-reproducibility-manifest.sh"
    ).read_text(encoding="utf-8")
    if "run-emulator-evidence.py\" reproducibility-artifacts" not in reproducibility:
        raise AssertionError("reproducibility manifest does not derive its artifact list")
    manifest = json.loads(
        (ROOT / "scripts" / "scenario-manifest.json").read_text(encoding="utf-8")
    )
    if "TOOLCHAIN_PROFILE.json" not in manifest.get("reproducibility_extras", []):
        raise AssertionError("reproducibility manifest lost the selected profile")
    print("Toolchain profile regression fixtures passed")


if __name__ == "__main__":
    main()
