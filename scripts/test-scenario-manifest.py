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
    generator = ROOT / "scripts/generate-evidence-matrix.py"
    generated = subprocess.run(["python3", str(generator)], capture_output=True, text=True)
    count = len(manifest["scenarios"])
    if generated.returncode or f"# mandatory-count\t{count}\n" not in generated.stdout:
        raise AssertionError(f"matrix generation did not cover the manifest: {generated}")
    with tempfile.TemporaryDirectory() as directory:
        test_manifest = Path(directory) / "manifest.json"
        output = Path(directory) / "fresh" / "matrix.tsv"
        published = subprocess.run(
            ["python3", str(generator), "--output", str(output)], capture_output=True, text=True,
        )
        if published.returncode or published.stdout or output.read_text() != generated.stdout:
            raise AssertionError(f"clean output directory was not populated: {published}")
        if output.stat().st_mode & 0o777 != 0o644:
            raise AssertionError("generated inventory changed the matrix's bundled file mode")

        def generate(change):
            copy = json.loads(json.dumps(manifest))
            change(copy)
            test_manifest.write_text(json.dumps(copy), encoding="utf-8")
            return subprocess.run(
                ["python3", str(generator), "--manifest", str(test_manifest)],
                capture_output=True, text=True,
            )

        for change, diagnostic in (
            (lambda m: m["scenarios"]["blocking-ipc"].pop("row"), "lacks a complete matrix row"),
            (lambda m: m["scenarios"]["blocking-ipc"].pop("tier"), "invalid matrix field tier"),
            (lambda m: m["scenarios"]["preemption"].update(tier="pr"), "exactly one scenario per runner"),
            (lambda m: m["scenarios"]["blocking-ipc"]["row"].update(image="../outside.iso"), "unsafe image path"),
            (lambda m: m["scenarios"]["blocking-ipc"]["row"].update(reason="bad\nrow"), "invalid matrix field reason"),
            (lambda m: m["scenarios"]["fast-entry-syscall"].update(row={}), "duplicates its family matrix row"),
        ):
            result = generate(change)
            if not result.returncode or result.stdout or diagnostic not in result.stderr:
                raise AssertionError(f"matrix generator did not fail before emitting output: {result}")

        def add_scenario(m):
            entry = json.loads(json.dumps(m["scenarios"]["return-flags-ac"]))
            entry["row"].update(
                image="leanos-@VERSION@-x86_64-return-new-fixture.iso",
                elf="leanos-return-new-fixture.elf",
                serial_log="return-new-fixture.serial.log",
                scenario="new-fixture", mode="27",
            )
            m["scenarios"]["return-new-fixture"] = entry

        result = generate(add_scenario)
        if result.returncode or f"# mandatory-count\t{count + 1}\n" not in result.stdout or "return-new-fixture\treturn\t" not in result.stdout:
            raise AssertionError(f"new manifest scenario needs a handwritten matrix edit: {result}")
        stale = Path(directory) / "stale.tsv"
        stale.write_text(generated.stdout.replace(f"# mandatory-count\t{count}", "# mandatory-count\t0"))
        result = subprocess.run(
            ["python3", str(generator), "--check", str(stale)], capture_output=True, text=True,
        )
        if not result.returncode or result.stdout or "derived evidence matrix is stale" not in result.stderr:
            raise AssertionError(f"matrix drift was not rejected: {result}")
        generate(lambda m: m["scenarios"]["blocking-ipc"].pop("row"))
        rejected = subprocess.run(
            ["python3", str(generator), "--manifest", str(test_manifest), "--output", str(output)],
            capture_output=True, text=True,
        )
        if not rejected.returncode or output.read_text() != generated.stdout:
            raise AssertionError("invalid manifest overwrote the last complete inventory")
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

    plan_rows = MODULE.prelink_plan_rows(manifest)
    if len(plan_rows) != len(images):
        raise AssertionError("prelink generation does not cover every image")
    extra = mutated(lambda m: m["build"]["images"].update({
        "leanos-new-fixture": dict(m["build"]["images"]["leanos"],
                                   prelink_plan="boot-page-plan-new-fixture.h")
    }))
    queried = run(extra, "prelink-plans")
    if queried.returncode or "leanos-new-fixture-prelink.elf\tboot-page-plan-new-fixture.h" not in queried.stdout:
        raise AssertionError("new manifest image requires a handwritten plan task")
    for change, diagnostic in (
        (lambda m: m["build"]["images"]["leanos"].pop("prelink_plan"), "missing or invalid prelink plan"),
        (lambda m: m["build"]["images"]["leanos"].update(prelink_plan="../outside.h"), "missing or invalid prelink plan"),
        (lambda m: m["build"]["images"]["leanos-preemption"].update(prelink_plan="boot-page-plan.h"), "same header twice"),
    ):
        rejected = run(mutated(change), "prelink-plans")
        if rejected.returncode == 0 or diagnostic not in rejected.stderr or rejected.stdout:
            raise AssertionError(f"prelink plan failed closed-output validation: {rejected}")

    for change, diagnostic in (
        (lambda m: m["build"]["images"]["leanos"].pop("plan_equal_to"), "lacks plan comparison declaration"),
        (lambda m: m["build"]["images"]["leanos"].update(plan_equal_to="leanos-absent"), "invalid plan comparison target"),
        (lambda m: m["build"]["images"]["leanos"].update(plan_equal_to="leanos"), "invalid plan comparison target"),
        (lambda m: m["build"]["images"]["leanos"].update(plan_equal_to=[]), "invalid plan comparison target"),
    ):
        rejected = run(mutated(change), "plan-comparisons")
        if rejected.returncode == 0 or diagnostic not in rejected.stderr or rejected.stdout:
            raise AssertionError(f"plan comparison accepted invalid input: {rejected}")
    extra["build"]["images"]["leanos-new-fixture"]["plan_equal_to"] = "leanos"
    compared = run(extra, "plan-comparisons")
    if compared.returncode or "boot-page-plan.h\tboot-page-plan-new-fixture.h" not in compared.stdout:
        raise AssertionError("new declared comparison requires a handwritten build check")

    for tier in ("pr", "all"):
        selected = MODULE.plan_check_rows(manifest, tier)
        for declared, row in zip(manifest["build"]["plan_checks"], selected):
            expected = declared.get("expected_full", declared["expected"]) if tier == "all" else declared["expected"]
            if row["expected"] != expected:
                raise AssertionError("final-plan query changed a tier's expected header")
    bad_full = mutated(lambda m: m["build"]["plan_checks"][0].update(expected_full="../outside.h"))
    rejected = run(bad_full, "plan-checks", "--tier", "pr")
    if rejected.returncode == 0 or rejected.stdout or "invalid full-tier expectation" not in rejected.stderr:
        raise AssertionError("invalid alternate expectation escaped validation in PR tier")

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

    for view, expected_count in (("plan-checks", len(manifest["build"]["plan_checks"])), ("disassemblies", len(manifest["build"]["disassemblies"])), ("entry-policies", len(manifest["build"]["entry_policies"])), ("extended-state-policies", len(manifest["build"]["extended_state_policies"]))):
        result = run(manifest, view)
        if result.returncode != 0 or len(result.stdout.splitlines()) != expected_count:
            raise AssertionError(f"{view} view does not mirror the manifest: {result.stderr}")
    converge = [row for row in MODULE.plan_check_rows(manifest) if row["check"] == "converge"]
    if not converge or any(row["targets"] == "-" for row in converge):
        raise AssertionError("plan convergence rows lack their graph targets")

    def view_rejects(view: str, transform, diagnostic: str) -> None:
        result = run(mutated(transform), view)
        if result.returncode == 0 or diagnostic not in result.stderr:
            raise AssertionError(f"{view}: expected {diagnostic!r}, got {result.stderr!r}")

    def unpackaged_plan(m):
        m["build"]["plan_checks"][0]["image"] = "leanos-never-packaged"

    view_rejects("plan-checks", unpackaged_plan, "build plan_checks names an unpackaged image 'leanos-never-packaged'")

    def bad_kind(m):
        m["build"]["plan_checks"][0]["check"] = "compare"

    view_rejects("plan-checks", bad_kind, "has unknown kind 'compare'")

    def converge_without_targets(m):
        for entry in m["build"]["plan_checks"]:
            if entry["check"] == "converge":
                entry["targets"] = []
                break

    view_rejects("plan-checks", converge_without_targets, "lists no graph targets")

    def non_graph_target(m):
        for entry in m["build"]["plan_checks"]:
            if entry["check"] == "converge":
                entry["targets"].append("leanos-double-fault-guard-mapped")
                break

    view_rejects("plan-checks", non_graph_target, "names a non-graph target 'leanos-double-fault-guard-mapped'")

    def duplicate_final(m):
        m["build"]["plan_checks"][1]["final"] = m["build"]["plan_checks"][0]["final"]

    view_rejects("plan-checks", duplicate_final, "write the same final plan twice")

    def duplicate_output(m):
        m["build"]["disassemblies"][1]["output"] = m["build"]["disassemblies"][0]["output"]

    view_rejects("disassemblies", duplicate_output, "write the same output twice")

    def duplicate_entry_key(m):
        m["build"]["entry_policies"][1]["key"] = m["build"]["entry_policies"][0]["key"]

    view_rejects("entry-policies", duplicate_entry_key, "keys are not unique")

    def bad_entry_environment(m):
        m["build"]["entry_policies"][0]["environment"] = ["probe"]

    view_rejects("entry-policies", bad_entry_environment, "environment must be a [name, value] pair")

    def bad_variant(m):
        m["build"]["extended_state_policies"][0]["variant"] = "x-87"

    view_rejects("extended-state-policies", bad_variant, "has a malformed variant or report")

    def missing_port_sites(m):
        m["build"]["packaged_images"]["leanos-nmi"]["port_sites"] = "direct-port-sites-absent.tsv"

    expect_rejection(mutated(missing_port_sites), "packaged image leanos-nmi port-sites inventory is missing: direct-port-sites-absent.tsv")

    def bad_port_sites(m):
        m["build"]["packaged_images"]["leanos-nmi"]["port_sites"] = "ports.tsv"

    expect_rejection(mutated(bad_port_sites), "packaged image leanos-nmi names a malformed port-sites inventory 'ports.tsv'")

    import hashlib
    inventories = sorted((ROOT / "scripts").glob("direct-port-sites*.tsv"))
    digests = {}
    for inventory in inventories:
        digests.setdefault(hashlib.sha256(inventory.read_bytes()).hexdigest(), []).append(inventory.name)
    duplicates = [names for names in digests.values() if len(names) > 1]
    if duplicates:
        raise AssertionError(f"byte-identical port-sites inventories must be shared: {duplicates}")
    declared = {entry.get("port_sites") for entry in manifest["build"]["packaged_images"].values()} - {None}
    for name in declared:
        if not (ROOT / "scripts" / name).is_file():
            raise AssertionError(f"declared port-sites inventory is missing: {name}")

    def missing_template(m):
        m["scenarios"]["blocking-ipc"]["expectations"] = "scripts/expectations/absent.transcript"

    view_rejects("expectations", missing_template, "scenario blocking-ipc expectation template is missing: scripts/expectations/absent.transcript")

    def bad_template(m):
        m["scenarios"]["blocking-ipc"]["expectations"] = "expectations.txt"

    view_rejects("expectations", bad_template, "scenario blocking-ipc names a malformed expectation template 'expectations.txt'")

    def misnamed_template(m):
        m["scenarios"]["preemption"]["expectations"] = "scripts/expectations/blocking-ipc.transcript"

    view_rejects("expectations", misnamed_template, "must be named after its boot scenario 'preemption'")

    def non_boot_template(m):
        m["scenarios"]["double-fault"]["expectations"] = "scripts/expectations/blocking-ipc.transcript"

    view_rejects("expectations", non_boot_template, "has an expectation template but is not a boot-runner row")

    def unlisted_template(m):
        del m["scenarios"]["blocking-ipc"]["expectations"]

    view_rejects("expectations", unlisted_template, "boot-runner scenario blocking-ipc has no expectation template")
    print("Scenario manifest build query fixtures passed")


if __name__ == "__main__":
    main()
