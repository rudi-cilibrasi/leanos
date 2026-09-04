#!/usr/bin/env python3
"""Controlled negatives for the scenario-manifest build query used by
scripts/build-image.sh: every malformed packaging or policy declaration fails
with a named diagnostic, and the derived rows mirror the manifest."""

from __future__ import annotations

import importlib.util
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/scenario-manifest.py"
SPEC = importlib.util.spec_from_file_location("scenario_manifest", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def run(manifest: dict, *arguments: str) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "manifest.json"
        path.write_text(json.dumps(manifest), encoding="utf-8")
        return subprocess.run(
            ["python3", str(SCRIPT), "--manifest", str(path), *arguments],
            capture_output=True, text=True,
        )


def expect_rejection(manifest: dict, diagnostic: str) -> None:
    result = run(manifest, "packaged-images")
    if result.returncode == 0:
        raise AssertionError(f"accepted a manifest that should fail: {diagnostic}")
    if diagnostic not in result.stderr:
        raise AssertionError(f"expected {diagnostic!r}, got {result.stderr!r}")


def main() -> None:
    manifest = json.loads((ROOT / "scripts/scenario-manifest.json").read_text(encoding="utf-8"))
    rows = MODULE.image_rows(manifest)
    images = manifest["build"]["images"]
    if [row["stem"] for row in rows] != list(images):
        raise AssertionError("derived image rows do not mirror the manifest order")
    for row in rows:
        entry = images[row["stem"]]
        if row["boot"] != entry["boot"] or row["kernel"] != entry["kernel"]:
            raise AssertionError(f"derived row for {row['stem']} does not mirror its objects")
    packaged = manifest["build"]["packaged_images"]
    packaged_rows = MODULE.packaged_rows(manifest)
    if [row["stem"] for row in packaged_rows] != list(packaged):
        raise AssertionError("derived packaged rows do not mirror the manifest order")
    for row in packaged_rows:
        entry = packaged[row["stem"]]
        if row["iso"] != entry["iso"] or row["grub"] != entry["grub"]:
            raise AssertionError(f"derived packaging for {row['stem']} disagrees with the manifest")
        if (entry.get("policy") is None) != (row["policy_key"] == "-"):
            raise AssertionError(f"derived policy for {row['stem']} disagrees with the manifest")
    listed = run(manifest, "packaged-images", "--version", "9.9.9")
    if listed.returncode != 0 or "@VERSION@" in listed.stdout or "leanos-9.9.9-x86_64.iso" not in listed.stdout:
        raise AssertionError("packaged-images subcommand did not substitute the version")
    plans = run(manifest, "page-plans")
    if plans.returncode != 0 or "boot-page-plan.h" not in plans.stdout.split():
        raise AssertionError("page-plans subcommand omits the canonical plan")
    if len(plans.stdout.split()) != len(set(plans.stdout.split())):
        raise AssertionError("page-plans subcommand repeats a header")

    def mutated(transform):
        copy = json.loads(json.dumps(manifest))
        transform(copy)
        return copy

    def unknown_kernel(m):
        m["build"]["images"]["leanos-preemption"]["kernel"] = "kernel-absent"

    expect_rejection(mutated(unknown_kernel), "image leanos-preemption links unknown kernel object 'kernel-absent'")

    def bad_iso(m):
        m["build"]["packaged_images"]["leanos-preemption"]["iso"] = "preemption.iso"

    expect_rejection(mutated(bad_iso), "packaged image leanos-preemption names an invalid iso 'preemption.iso'")

    def bad_grub(m):
        m["build"]["packaged_images"]["leanos-preemption"]["grub"] = "boot/grub-other.cfg"

    expect_rejection(mutated(bad_grub), "packaged image leanos-preemption names an unknown grub config 'boot/grub-other.cfg'")

    def duplicate_policy(m):
        m["build"]["packaged_images"]["leanos-preemption"]["policy"] = {"key": "canonical"}

    expect_rejection(mutated(duplicate_policy), "packaged image policy keys are not unique")

    def bad_environment(m):
        m["build"]["packaged_images"]["leanos-preemption"]["policy"] = {"key": "preemption", "environment": ["probe"]}

    expect_rejection(mutated(bad_environment), "packaged image leanos-preemption policy environment must be a [name, value] pair")

    def bad_extra(m):
        m["build"]["page_plan_stub_extras"].append("plan.h")

    result = run(mutated(bad_extra), "page-plans")
    if result.returncode == 0 or "page-plan stub extra 'plan.h' is not a plan header name" not in result.stderr:
        raise AssertionError("a malformed page-plan stub extra was accepted")

    def no_build(m):
        del m["build"]

    expect_rejection(mutated(no_build), "scenario manifest lacks build images")
    print("Scenario manifest build query fixtures passed")


if __name__ == "__main__":
    main()
