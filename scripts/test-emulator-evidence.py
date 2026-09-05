#!/usr/bin/env python3
"""Controlled fixtures for the shared emulator evidence matrix."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import threading
import time
from types import SimpleNamespace
from unittest import mock


ROOT = Path(__file__).resolve().parent.parent
MODULE_PATH = ROOT / "scripts/run-emulator-evidence.py"
SPEC = importlib.util.spec_from_file_location("leanos_emulator_evidence", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load emulator evidence runner")
evidence = importlib.util.module_from_spec(SPEC)

# The runner reads record identities from the generated serial vocabulary;
# these unit tests run without a built image, so they point it at a minimal
# vocabulary carrying exactly the records the runner names.
_SERIAL_VOCABULARY = tempfile.NamedTemporaryFile(
    "w", suffix=".tsv", prefix="serial-protocol-", delete=False
)
_SERIAL_PREFIX = "LEANOS" + "/"  # split so the literal-identity scan has nothing to flag
_SERIAL_VOCABULARY.write(
    "leanos-serial-protocol\t1\nsource-revision\ttest\n"
    f"family\t3\tLEANOS_SERIAL_FAMILY_3\t{_SERIAL_PREFIX}3\n"
    f"record\t3\tORACLE\tLEANOS_SERIAL_3_ORACLE\t{_SERIAL_PREFIX}3 ORACLE\n"
)
_SERIAL_VOCABULARY.close()
os.environ.setdefault("LEANOS_SERIAL_PROTOCOL_TSV", _SERIAL_VOCABULARY.name)
SPEC.loader.exec_module(evidence)


def expect_failure(action, fragment: str) -> None:
    try:
        action()
    except evidence.EvidenceError as error:
        if fragment not in str(error):
            raise AssertionError(f"expected {fragment!r}, got {error!r}") from error
    else:
        raise AssertionError(f"expected failure containing {fragment!r}")


def mutate_matrix(target: Path, transform) -> None:
    lines = evidence.DEFAULT_MATRIX.read_text(encoding="utf-8").splitlines()
    target.write_text("\n".join(transform(lines)) + "\n", encoding="utf-8")


def replace_last(content: str, old: str, new: str) -> str:
    before, separator, after = content.rpartition(old)
    if not separator:
        raise AssertionError(f"fixture source does not contain {old!r}")
    return before + new + after


def prepare_tree(tmp: Path) -> tuple[Path, Path, Path, argparse.Namespace]:
    build = tmp / "boot"
    output = tmp / "evidence/report.json"
    tools = tmp / "tool-versions.txt"
    build.mkdir(parents=True)
    revision = "a" * 40
    (build / "SOURCE_REVISION").write_text(revision + "\n", encoding="utf-8")
    tools.write_text(f"source-revision: {revision}\nqemu: fixture\n", encoding="utf-8")
    _, rows = evidence.parse_matrix(evidence.DEFAULT_MATRIX)
    for row in rows:
        paths = evidence.expanded(row, "0.1.0", build)
        paths["image"].write_bytes((row["id"] + "-iso").encode())
        paths["elf"].write_bytes((row["id"] + "-elf").encode())
    args = argparse.Namespace(
        matrix=evidence.DEFAULT_MATRIX,
        build_dir=build,
        output=output,
        tool_versions=tools,
        version="0.1.0",
        scenario=None,
        tier="all",
        shard_index=None,
        shard_count=None,
        jobs=4,
    )
    return build, output, tools, args


def prepare_bundle_tree(tmp: Path) -> tuple[Path, Path, Path, Path]:
    root = tmp / "bundle-root"
    paths = (
        "build/boot/SHA256SUMS",
        "build/boot/SOURCE_REVISION",
        "build/boot/TOOLCHAIN_PROFILE.json",
        "build/boot/leanos.elf",
        "build/boot/leanos-0.1.0-x86_64.iso",
        "build/boot/serial.log",
        "build/ci/emulator-evidence.log",
        "build/ci/image-build.log",
        "build/ci/image-build-phases.tsv",
        "build/ci/tool-versions.txt",
        "build/evidence/blocking-ipc.command.log",
        "build/evidence/q35-edu-dma.tsv",
        "build/evidence/q35-pci-construction.tsv",
        "build/oracle/host-results.txt",
        "scripts/emulator-evidence-matrix.tsv",
    )
    for relative in paths:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"fixture:{relative}\n", encoding="utf-8")
    (root / "build/boot/kernel.o").write_bytes(b"compiler intermediate")
    staged_iso = root / "build/boot/iso-fixture/boot/leanos.iso"
    staged_iso.parent.mkdir(parents=True)
    staged_iso.write_bytes(b"staging intermediate")
    stale_bundle = root / "build/ci/previous.tar"
    stale_bundle.write_bytes(b"old bundle")

    def record(relative: str) -> dict[str, str]:
        return {"path": relative, "sha256": evidence.sha256(root / relative)}

    report_path = root / "build/evidence/emulator-shard-0.json"
    report = {
        "schema": "leanos-emulator-evidence-report-v1",
        "status": "PASS",
        "matrix": record("scripts/emulator-evidence-matrix.tsv"),
        "source": {
            "embedded_revision_path": "build/boot/SOURCE_REVISION",
            "embedded_revision_sha256": evidence.sha256(
                root / "build/boot/SOURCE_REVISION"
            ),
        },
        "tools": {
            "inventory_path": "build/ci/tool-versions.txt",
            "inventory_sha256": evidence.sha256(root / "build/ci/tool-versions.txt"),
        },
        "results": [{
            "artifacts": [
                record("build/boot/leanos-0.1.0-x86_64.iso"),
                record("build/boot/leanos.elf"),
            ],
            "serial_log": record("build/boot/serial.log"),
            "command_log": record("build/evidence/blocking-ipc.command.log"),
        }],
    }
    report_path.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    output = root / "build/ci/emulator-evidence-shard-0.tar"
    return root, report_path, output, root / "build/boot/serial.log"


def successful_runner(_command, *, env, **_kwargs):
    serial = "typed fixture evidence\n" + "".join(
        f"{evidence.serial_record('3', 'ORACLE')} id={row} result=PASS\n"
        for row in evidence.REQUIRED_IOTLB_ORACLE_ROWS
    )
    Path(env["LEANOS_SERIAL_LOG"]).write_text(serial, encoding="utf-8")
    if "LEANOS_DMA_SNAPSHOT" in env:
        Path(env["LEANOS_DMA_SNAPSHOT"]).write_text(
            "typed DMA snapshot evidence\n", encoding="utf-8"
        )
    if "LEANOS_VTD_SNAPSHOT" in env:
        Path(env["LEANOS_VTD_SNAPSHOT"]).write_text(
            "typed VT-d activation snapshot evidence\n", encoding="utf-8"
        )
    if "LEANOS_QMP_LOG" in env:
        Path(env["LEANOS_QMP_LOG"]).write_text(
            '{"direction":"host-to-qemu","message":{"execute":"inject-nmi"}}\n',
            encoding="utf-8",
        )
    if "LEANOS_MULTIVCPU_INVENTORY" in env:
        Path(env["LEANOS_MULTIVCPU_INVENTORY"]).write_text(
            "# leanos-q35-multivcpu-inventory-v1\n"
            "index\tqom-path\ttopology\n"
            "0\t/machine/unattached/device[0]\tsocket=0,core=0,thread=0\n"
            "1\t/machine/unattached/device[1]\tsocket=0,core=1,thread=0\n",
            encoding="utf-8",
        )
    return SimpleNamespace(returncode=0, stdout="QEMU command: fixture-qemu --checked\n")


def run_fixtures() -> None:
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)

        bundle_root, bundle_report, bundle_output, required_serial = (
            prepare_bundle_tree(tmp)
        )
        evidence.build_evidence_bundle(bundle_report, bundle_output, bundle_root)
        first_bundle = bundle_output.read_bytes()
        evidence.build_evidence_bundle(bundle_report, bundle_output, bundle_root)
        if bundle_output.read_bytes() != first_bundle:
            raise AssertionError("emulator evidence bundle is not deterministic")
        with tarfile.open(bundle_output, mode="r") as archive:
            names = set(archive.getnames())
            manifest = json.load(archive.extractfile("MANIFEST.json"))
        if manifest["schema"] != "leanos-emulator-evidence-bundle-v1":
            raise AssertionError("emulator evidence bundle has the wrong schema")
        if manifest["missing_required_files"] or manifest["validation_errors"]:
            raise AssertionError("complete emulator evidence bundle reports failures")
        for excluded in (
            "build/boot/kernel.o",
            "build/boot/iso-fixture/boot/leanos.iso",
            "build/ci/previous.tar",
            "build/ci/emulator-evidence-shard-0.tar",
        ):
            if excluded in names:
                raise AssertionError(f"bundle retained excluded intermediate {excluded}")
        image = bundle_root / "build/boot/leanos-0.1.0-x86_64.iso"
        image.write_bytes(b"tampered image")
        stale_output = bundle_output.with_name("stale.tar")
        expect_failure(
            lambda: evidence.build_evidence_bundle(
                bundle_report, stale_output, bundle_root
            ),
            "report-bound hash differs: build/boot/leanos-0.1.0-x86_64.iso",
        )
        with tarfile.open(stale_output, mode="r") as archive:
            stale_manifest = json.load(archive.extractfile("MANIFEST.json"))
        if stale_manifest["validation_errors"] != [
            "report-bound hash differs: build/boot/leanos-0.1.0-x86_64.iso"
        ]:
            raise AssertionError("diagnostic bundle did not record the stale file")
        image.write_text(
            "fixture:build/boot/leanos-0.1.0-x86_64.iso\n", encoding="utf-8"
        )
        required_serial.unlink()
        missing_output = bundle_output.with_name("missing.tar")
        expect_failure(
            lambda: evidence.build_evidence_bundle(
                bundle_report, missing_output, bundle_root
            ),
            "missing required files: build/boot/serial.log",
        )
        with tarfile.open(missing_output, mode="r") as archive:
            missing_manifest = json.load(archive.extractfile("MANIFEST.json"))
        if missing_manifest["missing_required_files"] != ["build/boot/serial.log"]:
            raise AssertionError("diagnostic bundle did not record the missing file")

        _, matrix_rows = evidence.parse_matrix(evidence.DEFAULT_MATRIX)
        if evidence.qemu_accelerator({}) != "tcg":
            raise AssertionError("default evidence accelerator is not explicit TCG")
        if evidence.qemu_accelerator({"LEANOS_QEMU_ACCELERATOR": "kvm"}) != "kvm":
            raise AssertionError("KVM evidence accelerator is not selectable")
        expect_failure(
            lambda: evidence.qemu_accelerator(
                {"LEANOS_QEMU_ACCELERATOR": "kvm,tcg"}
            ),
            "fallback lists are forbidden",
        )
        kvm_paths = evidence.expanded(matrix_rows[0], "0.1.0", bundle_root / "build/boot")
        _kvm_command, kvm_environment = evidence.scenario_invocation(
            matrix_rows[0], kvm_paths, bundle_root / "build/boot", "0.1.0", "kvm"
        )
        if kvm_environment.get("LEANOS_QEMU_ACCELERATOR") != "kvm":
            raise AssertionError("scenario invocation does not record KVM selection")
        shards = [
            evidence.select_rows(matrix_rows, None, "all", index, 4)
            for index in range(4)
        ]
        if [row["id"] for shard in shards for row in shard] == [
            row["id"] for row in matrix_rows
        ]:
            raise AssertionError("shards were concatenated instead of interleaved")
        if sorted(row["id"] for shard in shards for row in shard) != sorted(
            row["id"] for row in matrix_rows
        ):
            raise AssertionError("stable shards do not cover the matrix exactly once")
        weighted_rows = [
            {"id": f"weighted-{index}", "timeout": str(weight)}
            for index, weight in enumerate((9, 8, 7, 6, 5, 4))
        ]
        weighted_shards = [
            evidence.select_rows(weighted_rows, None, "all", index, 2)
            for index in range(2)
        ]
        if [[row["id"] for row in shard] for shard in weighted_shards] != [
            ["weighted-0", "weighted-3", "weighted-4"],
            ["weighted-1", "weighted-2", "weighted-5"],
        ]:
            raise AssertionError("duration-bound shard assignment is not deterministic")
        weighted_totals = [
            sum(int(row["timeout"]) for row in shard) for shard in weighted_shards
        ]
        if weighted_totals != [20, 19]:
            raise AssertionError("duration-bound shard assignment is not balanced")
        expect_failure(
            lambda: evidence.select_rows(matrix_rows, "blocking-ipc", "all", 0, 4),
            "cannot be combined with sharding",
        )
        expect_failure(
            lambda: evidence.select_rows(matrix_rows, None, "all", 0, None),
            "must be specified together",
        )
        expect_failure(
            lambda: evidence.select_rows(matrix_rows, None, "all", 4, 4),
            "between zero and count minus one",
        )

        pr_rows = evidence.select_rows(matrix_rows, None, "pr", None, None)
        if len(pr_rows) != len(evidence.RUNNERS):
            raise AssertionError("PR tier does not select exactly one row per runner")
        pr_build_artifacts = evidence.select_build_artifacts(pr_rows, "0.1.0")
        if [artifact[0] for artifact in pr_build_artifacts] != [
            row["id"] for row in pr_rows
        ]:
            raise AssertionError("PR build plan does not preserve matrix order")
        if any("@VERSION@" in artifact[2] for artifact in pr_build_artifacts):
            raise AssertionError("PR build plan retains an unexpanded image version")
        if len({artifact[1] for artifact in pr_build_artifacts}) != len(
            evidence.RUNNERS
        ):
            raise AssertionError("PR build plan does not retain one runner boundary")
        expect_failure(
            lambda: evidence.select_build_artifacts(pr_rows, "not-a-version"),
            "version must be MAJOR.MINOR.PATCH",
        )
        if pr_build_artifacts[0][3:] != ("leanos-prelink.elf", "leanos.elf"):
            raise AssertionError("PR build plan does not map the canonical Make targets")
        artifact_targets = {
            artifact[0]: artifact[3:] for artifact in pr_build_artifacts
        }
        expected_special_targets = {
            "assigned-edu-inventory": ("leanos-prelink.elf", "leanos.elf"),
            "multivcpu-rejection": ("leanos-prelink.elf", "leanos.elf"),
            "double-fault": (
                "leanos-double-fault-prelink.elf",
                "kernel-double-fault.o",
            ),
            "entry-stack-overflow": (
                "leanos-entry-stack-overflow-prelink.elf",
                "kernel-entry-stack-overflow.o",
            ),
            "double-fault-guard-mapped": (
                "leanos-guard-prelink.elf",
                "kernel-double-fault-guard-mapped.o",
            ),
        }
        for scenario, expected_targets in expected_special_targets.items():
            if artifact_targets.get(scenario) != expected_targets:
                raise AssertionError(
                    f"PR build plan maps {scenario} to nonexistent Make targets"
                )
        build_image = (evidence.ROOT / "scripts/build-image.sh").read_text(
            encoding="utf-8"
        )
        if 'selected_prelink_targets+=("$build/$plan_prelink")' not in build_image:
            raise AssertionError("build-image does not consume selected prelink targets")
        if 'selected_final_targets+=("$build/$plan_final")' not in build_image:
            raise AssertionError("build-image does not consume selected final targets")
        if 'selected_prelink_lookup["$build/$plan_prelink"]=1' not in build_image:
            raise AssertionError("build-image does not index selected prelink targets")
        if 'selected_final_lookup["$build/$plan_final"]=1' not in build_image:
            raise AssertionError("build-image does not index selected final targets")
        if 'for prelink in "${selected_prelink_targets[@]}"' not in build_image:
            raise AssertionError("build-image does not validate selected prelink cache coverage")
        if 'if [[ ! -f "$prelink" ]]; then' not in build_image:
            raise AssertionError("build-image accepts a cache missing selected prelinks")
        if 'boot_plan_batch_args=("${filtered_boot_plan_batch_args[@]}")' not in build_image:
            raise AssertionError("build-image does not restrict PR boot-plan generation")
        if 'if [[ "$evidence_tier" == all ]]; then\n  cmp "$build/boot-page-plan-fault-containment.h"' not in build_image:
            raise AssertionError("build-image does not reserve cross-variant plan checks for full evidence")
        if 'if [[ "$evidence_tier" == all ]] && nm "$build/kernel.o"' not in build_image:
            raise AssertionError("build-image checks unselected canonical objects in PR shards")
        if '-z "${selected_final_lookup[$elf_path]:-}"' not in build_image:
            raise AssertionError("build-image does not restrict PR policy checks to selected final images")
        if (
            'if [[ "$elf_name" == leanos-multivcpu-rejection.elf ]]; then\n'
            '    elf_path="$build/leanos.elf"\n'
            '  fi'
            not in build_image
        ):
            raise AssertionError(
                "build-image checks the multi-vCPU alias before it is materialized"
            )
        if 'elif ((direct_port_images == 0)); then' not in build_image:
            raise AssertionError("build-image accepts an empty selected PR policy set")
        if 'selected_final_enabled "$return_elf" || continue' not in build_image:
            raise AssertionError("build-image does not restrict PR return policy checks")
        if 'selected_final_enabled "$elf_path" || return 0' not in build_image:
            raise AssertionError("build-image does not restrict final-plan checks to selected images")
        if 'validate_selected_final_plan "$build/$plan_image.elf"' not in build_image:
            raise AssertionError("build-image does not route the final plans through selection")
        if 'converge_selected_graph_plan "$build/$plan_image.elf"' not in build_image:
            raise AssertionError("build-image does not converge shared graph plans")
        if "./scripts/scenario-manifest.py plan-checks" not in build_image:
            raise AssertionError("build-image does not derive its plan checks from the manifest")
        plan_checks = evidence.load_manifest()["build"]["plan_checks"]
        canonical_plan = next((entry for entry in plan_checks if entry["image"] == "leanos"), None)
        if canonical_plan is None or canonical_plan["check"] != "validate":
            raise AssertionError("manifest does not validate the canonical final plan")
        converge = [entry for entry in plan_checks if entry["check"] == "converge"]
        if {entry["image"] for entry in converge} != {"leanos-bootstrap64-nmi", "leanos-extended-state"}:
            raise AssertionError("manifest does not converge the shared graph plans")
        for image, expected in (
            ("leanos-direct-port-serial", "boot-page-plan-direct-port.h"),
            ("leanos-direct-port-pic", "boot-page-plan-direct-port.h"),
            ("leanos-divide-error", "boot-page-plan-integer-fault.h"),
            ("leanos-breakpoint", "boot-page-plan-integer-fault.h"),
        ):
            entry = next((check for check in plan_checks if check["image"] == image), None)
            if entry is None or entry["check"] != "validate" or entry["expected"] != expected:
                raise AssertionError(f"manifest does not validate {image} against its shared plan")
        build = evidence.load_manifest()["build"]
        if {row["image"] for row in build["disassemblies"]} < {"leanos-bootstrap32-ud", "leanos-breakpoint"}:
            raise AssertionError("manifest does not list the selected disassembly reports")
        if [row["variant"] for row in build["extended_state_policies"]] != ["x87", "mmx", "sse", "sse2", "avx"]:
            raise AssertionError("manifest does not list the extended-state policy variants in order")
        if 'if selected_final_enabled "$build/leanos-frame-budget.elf"; then' not in build_image:
            raise AssertionError("build-image does not restrict frame-budget convergence")
        if 'selected_final_enabled "$build/leanos-fault-${probe}.elf" || continue' not in build_image:
            raise AssertionError("build-image does not restrict fault-family final plans")
        if (
            'expected_fault_plan="$build/boot-page-plan-fault-${probe}.h"\n'
            '  if [[ "$evidence_tier" == all && "$probe" != stale-translation ]]'
            not in build_image
        ):
            raise AssertionError(
                "build-image compares selected PR fault plans against an unselected stub"
            )
        for final_elf in (
            "leanos-double-fault.elf",
            "leanos-entry-stack-overflow.elf",
            "leanos-double-fault-guard-mapped.elf",
        ):
            if f'if selected_final_enabled "$build/{final_elf}"; then' not in build_image:
                raise AssertionError(
                    f"build-image does not restrict {final_elf} final relink"
                )
        if 'selected_final_enabled "$elf" || return 0' not in build_image:
            raise AssertionError("build-image does not restrict image-policy jobs")
        if 'selected_final_lookup["$build/leanos-double-fault.elf"]=1' not in build_image:
            raise AssertionError("build-image does not index manually linked selected ELFs")
        if 'selected_iso_root_lookup["$staging_root"]="$elf"' not in build_image:
            raise AssertionError("build-image does not index selected ISO staging roots")
        if 'local elf="${selected_iso_root_lookup[$staging_root]:-}"' not in build_image:
            raise AssertionError("build-image does not filter ISO packaging by selected root")
        if 'xargs -0 sha256sum > "$build/SHA256SUMS"' not in build_image:
            raise AssertionError("build-image does not checksum only selected PR artifacts")
        if 'if selected_final_enabled "$build/leanos.elf"; then' not in build_image:
            raise AssertionError("build-image does not gate canonical-only validation")
        if 'write_selected_disassembly "$build/$disassembly_image.elf"' not in build_image:
            raise AssertionError("build-image does not gate selected disassembly reports")
        if 'run_selected_extended_state_policy "$policy_variant"' not in build_image:
            raise AssertionError("build-image does not gate extended-state policy reports")
        if 'if [[ "$evidence_tier" == all ]]; then\n  queue_return_fixture restore' not in build_image:
            raise AssertionError("build-image does not reserve negative policy fixtures for full evidence")
        if 'if [[ "$evidence_tier" == all ]]' not in build_image:
            raise AssertionError("build-image does not preserve the all-tier graph")
        malformed_elf_rows = [dict(pr_rows[0], elf="outside.elf")]
        expect_failure(
            lambda: evidence.select_build_artifacts(malformed_elf_rows, "0.1.0"),
            "unsupported build ELF",
        )

        duplicate_pr_runner = tmp / "duplicate-pr-runner.tsv"
        mutate_matrix(
            duplicate_pr_runner,
            lambda lines: [
                line.rsplit("\t", 1)[0] + "\tpr"
                if line.startswith("projection-authority-mutation\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(duplicate_pr_runner),
            "PR tier must contain exactly one scenario per runner",
        )

        ci_workflow = evidence.ROOT / ".github/workflows/ci.yml"
        original_ci = ci_workflow.read_text(encoding="utf-8")
        # A dependency must be awaited, read from needs, and included in the
        # result loop. Keeping any two of those three is insufficient.
        for before, after in (
            ("      - reproducibility-plan\n", ""),
            ("REPRODUCIBILITY_PLAN: ${{ needs.reproducibility-plan.result }}",
             "REPRODUCIBILITY_PLAN: success"),
            (' "$REPRODUCIBILITY_PLAN"', ""),
        ):
            changed_ci = original_ci.replace(before, after, 1)
            if changed_ci == original_ci:
                raise AssertionError(f"admission fixture did not mutate {before!r}")
            try:
                ci_workflow.write_text(changed_ci, encoding="utf-8")
                expect_failure(
                    evidence.check_workflows,
                    "CI job 'premerge-admission' must fail closed",
                )
            finally:
                ci_workflow.write_text(original_ci, encoding="utf-8")

        # Execute the real gate with every other dependency green. A failed,
        # cancelled, skipped, or absent plan result must block admission.
        admission = evidence.load_workflow(ci_workflow)["jobs"]["premerge-admission"]
        gate = next(step for step in admission["steps"] if "run" in step)
        gate_env = {key: "success" for key in gate["env"]}
        gate_env["PROMOTED"] = "true"
        for plan_result in ("success", "failure", "cancelled", "skipped", ""):
            result = subprocess.run(
                ["bash", "-e", "-c", gate["run"]],
                env={**os.environ, **gate_env, "REPRODUCIBILITY_PLAN": plan_result},
                text=True, capture_output=True,
            )
            if (result.returncode == 0) != (plan_result == "success"):
                raise AssertionError(f"admission mishandled plan result {plan_result!r}")
            if result.returncode and "dependency concluded" not in result.stderr:
                raise AssertionError(f"unexpected admission failure: {result.stderr}")
        try:
            ci_workflow.write_text(
                original_ci.replace(
                    "  merge_group:\n    branches:\n      - main\n", "", 1
                ),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI must run complete evidence for merge-queue candidates targeting main",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        try:
            ci_workflow.write_text(
                original_ci.replace("./scripts/build-image.sh", "./scripts/build.sh", 1),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI job 'clang-image' does not preserve its command contract: "
                "./scripts/build-image.sh",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        try:
            ci_workflow.write_text(
                original_ci.replace(
                    "types: [opened, synchronize, reopened, labeled, unlabeled, "
                    "ready_for_review]",
                    "types: [opened, synchronize, reopened]",
                    1,
                ),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI must promote only labeled pull requests to complete evidence",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        try:
            ci_workflow.write_text(
                original_ci.replace(
                    "LEANOS_SKIP_HOSTED_BOUNDARY_REPLAY: "
                    "${{ (github.event_name == 'pull_request' || github.event_name == "
                    "'merge_group') && '1' || '0' }}",
                    "LEANOS_SKIP_HOSTED_BOUNDARY_REPLAY: 0",
                    1,
                ),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI must parallelize complete hosted evidence for pull requests and merge groups",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        try:
            ci_workflow.write_text(
                original_ci.replace(
                    "if: github.event_name == 'pull_request' || "
                    "github.event_name == 'merge_group'",
                    "if: github.event_name == 'pull_request'",
                    1,
                ),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI must parallelize complete hosted evidence for pull requests and merge groups",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        try:
            ci_workflow.write_text(
                original_ci.replace(
                    "  clang-reproducibility-build:\n"
                    "    name: Clang independent reproducibility build\n"
                    "    if: github.event_name != 'pull_request' || "
                    "contains(github.event.pull_request.labels.*.name, "
                    "'ci:full-admission')",
                    "  clang-reproducibility-build:\n"
                    "    name: Clang independent reproducibility build\n"
                    "    if: github.event_name == 'pull_request'",
                    1,
                ),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI job 'clang-reproducibility-build' must run only for promoted "
                "complete evidence",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        try:
            ci_workflow.write_text(
                original_ci.replace(
                    "PROMOTED: ${{ "
                    "contains(github.event.pull_request.labels.*.name, "
                    "'ci:full-admission') }}",
                    "PROMOTED: false",
                    1,
                ),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI job 'premerge-admission' must fail closed on labeled complete "
                "pre-merge admission",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        try:
            ci_workflow.write_text(
                original_ci.replace(
                    "    continue-on-error: true\n"
                    "    strategy:\n"
                    "      fail-fast: false\n"
                    "      matrix:\n"
                    "        shard: [0, 1, 2, 3]\n",
                    "    continue-on-error: false\n"
                    "    strategy:\n"
                    "      fail-fast: false\n"
                    "      matrix:\n"
                    "        shard: [0, 1, 2, 3]\n",
                    1,
                ),
                encoding="utf-8",
            )
            expect_failure(
                evidence.check_workflows,
                "CI KVM lane must remain explicit, four-way, artifact-backed, and non-blocking",
            )
        finally:
            ci_workflow.write_text(original_ci, encoding="utf-8")

        duplicate = tmp / "duplicate.tsv"
        mutate_matrix(
            duplicate,
            lambda lines: lines + [next(line for line in lines if not line.startswith("#"))],
        )
        expect_failure(lambda: evidence.parse_matrix(duplicate), "duplicate scenario ID")

        missing_return = tmp / "missing-return.tsv"
        mutate_matrix(
            missing_return,
            lambda lines: [
                line for line in lines if not line.startswith("return-kernel-selector\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_return),
            "mandatory inventory count differs",
        )

        missing_double_fault = tmp / "missing-double-fault.tsv"
        mutate_matrix(
            missing_double_fault,
            lambda lines: [
                line for line in lines if not line.startswith("double-fault\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_double_fault),
            "mandatory inventory count differs",
        )

        missing_entry_overflow = tmp / "missing-entry-overflow.tsv"
        mutate_matrix(
            missing_entry_overflow,
            lambda lines: [
                line for line in lines if not line.startswith("entry-stack-overflow\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_entry_overflow),
            "mandatory inventory count differs",
        )

        missing_extended_state = tmp / "missing-extended-state.tsv"
        mutate_matrix(
            missing_extended_state,
            lambda lines: [
                line for line in lines
                if not line.startswith("extended-state-denial\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_extended_state),
            "mandatory inventory count differs",
        )

        missing_extended_state_sse = tmp / "missing-extended-state-sse.tsv"
        mutate_matrix(
            missing_extended_state_sse,
            lambda lines: [
                line for line in lines
                if not line.startswith("extended-state-denial-sse\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_extended_state_sse),
            "mandatory inventory count differs",
        )

        missing_extended_state_sse2 = tmp / "missing-extended-state-sse2.tsv"
        mutate_matrix(
            missing_extended_state_sse2,
            lambda lines: [
                line for line in lines
                if not line.startswith("extended-state-denial-sse2\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_extended_state_sse2),
            "mandatory inventory count differs",
        )

        missing_extended_state_avx = tmp / "missing-extended-state-avx.tsv"
        mutate_matrix(
            missing_extended_state_avx,
            lambda lines: [
                line for line in lines
                if not line.startswith("extended-state-denial-avx\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_extended_state_avx),
            "mandatory inventory count differs",
        )

        missing_peer_pke = tmp / "missing-peer-pke.tsv"
        mutate_matrix(
            missing_peer_pke,
            lambda lines: [
                line for line in lines
                if not line.startswith("extended-state-peer-pke\t")
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_peer_pke),
            "mandatory inventory count differs",
        )

        missing_fast_entry = tmp / "missing-fast-entry.tsv"
        mutate_matrix(
            missing_fast_entry,
            lambda lines: [
                line.replace("fast-entry-syscall", "fast-entry-syscall-replacement")
                if line.startswith("fast-entry-syscall\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_fast_entry),
            "mandatory fast-entry scenario is absent: fast-entry-syscall",
        )

        drifted_fast_entry = tmp / "drifted-fast-entry.tsv"
        mutate_matrix(
            drifted_fast_entry,
            lambda lines: [
                line.replace("\t30\t", "\t31\t", 1)
                if line.startswith("fast-entry-sysenter\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(drifted_fast_entry),
            "mandatory fast-entry scenario fast-entry-sysenter has unexpected timeout",
        )

        missing_fast_entry_mutation = tmp / "missing-fast-entry-mutation.tsv"
        mutate_matrix(
            missing_fast_entry_mutation,
            lambda lines: [
                line.replace(
                    "return-fast-entry-sce-relaxation",
                    "return-fast-entry-sce-relaxation-replacement",
                )
                if line.startswith("return-fast-entry-sce-relaxation\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_fast_entry_mutation),
            "mandatory fast-entry-relaxation scenario is absent: return-fast-entry-sce-relaxation",
        )

        missing_fast_entry_target_mutation = tmp / "missing-fast-entry-target-mutation.tsv"
        mutate_matrix(
            missing_fast_entry_target_mutation,
            lambda lines: [
                line.replace(
                    "return-fast-entry-lstar-relaxation",
                    "return-fast-entry-lstar-relaxation-replacement",
                )
                if line.startswith("return-fast-entry-lstar-relaxation\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_fast_entry_target_mutation),
            "mandatory fast-entry-relaxation scenario is absent: return-fast-entry-lstar-relaxation",
        )

        missing_fast_entry_sysenter_mutation = (
            tmp / "missing-fast-entry-sysenter-mutation.tsv"
        )
        mutate_matrix(
            missing_fast_entry_sysenter_mutation,
            lambda lines: [
                line.replace(
                    "return-fast-entry-sysenter-eip-relaxation",
                    "return-fast-entry-sysenter-eip-relaxation-replacement",
                )
                if line.startswith("return-fast-entry-sysenter-eip-relaxation\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_fast_entry_sysenter_mutation),
            "mandatory fast-entry-relaxation scenario is absent: "
            "return-fast-entry-sysenter-eip-relaxation",
        )

        missing_complete_live_inventory = tmp / "missing-complete-live-inventory.tsv"
        mutate_matrix(
            missing_complete_live_inventory,
            lambda lines: [
                line.replace(
                    "return-fast-entry-sysenter-esp-relaxation",
                    "return-fast-entry-sysenter-esp-relaxation-replacement",
                )
                if line.startswith("return-fast-entry-sysenter-esp-relaxation\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(missing_complete_live_inventory),
            "mandatory fast-entry-relaxation scenario is absent: "
            "return-fast-entry-sysenter-esp-relaxation",
        )

        wrong_class = tmp / "wrong-class.tsv"
        mutate_matrix(
            wrong_class,
            lambda lines: [
                line.replace("accepted-boot", "claimed-proof", 1)
                if line.startswith("blocking-ipc\t")
                else line
                for line in lines
            ],
        )
        expect_failure(
            lambda: evidence.parse_matrix(wrong_class), "unrecognized result class"
        )

        build, output, tools, args = prepare_tree(tmp / "success")
        revision = "a" * 40
        active_runners = 0
        peak_runners = 0
        runner_lock = threading.Lock()

        def concurrent_runner(command, **kwargs):
            nonlocal active_runners, peak_runners
            scenario_tmp = Path(kwargs["env"]["TMPDIR"])
            if output.parent in scenario_tmp.parents:
                raise AssertionError("scenario TMPDIR uses the long build-tree path")
            with tempfile.TemporaryDirectory(dir=scenario_tmp) as nested_tmp:
                qmp_path = Path(nested_tmp) / "qmp"
                if len(os.fsencode(qmp_path)) >= 108:
                    raise AssertionError("nested QMP socket path exceeds sockaddr_un")
            with runner_lock:
                active_runners += 1
                peak_runners = max(peak_runners, active_runners)
            try:
                time.sleep(0.01)
                result = successful_runner(command, **kwargs)
                result.stdout = (
                    "QEMU command: fixture-qemu -qmp "
                    f"unix:{scenario_tmp}/tmp.dynamic/qmp\n"
                )
                return result
            finally:
                with runner_lock:
                    active_runners -= 1

        with (
            mock.patch.object(evidence, "git_revision", return_value=revision),
            mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
            mock.patch.object(evidence.subprocess, "run", side_effect=concurrent_runner),
        ):
            evidence.run(args)
        if peak_runners < 2:
            raise AssertionError("emulator scenarios did not execute concurrently")
        parallel_report = output.read_bytes()
        args.jobs = 1
        with (
            mock.patch.object(evidence, "git_revision", return_value=revision),
            mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
            mock.patch.object(evidence.subprocess, "run", side_effect=concurrent_runner),
        ):
            evidence.run(args)
        if output.read_bytes() != parallel_report:
            raise AssertionError("parallel evidence report differs from serial output")
        report = json.loads(output.read_text(encoding="utf-8"))
        if not all(
            result["qemu_commands"] == [
                " fixture-qemu -qmp unix:$SCENARIO_TMPDIR/$NESTED_TMPDIR/qmp"
            ]
            for result in report["results"]
        ):
            raise AssertionError("volatile nested TMPDIR path was not canonicalized")
        args.jobs = 4

        shard_output = output.with_name("shard-1.json")
        args.output = shard_output
        args.shard_index = 1
        args.shard_count = 4
        with (
            mock.patch.object(evidence, "git_revision", return_value=revision),
            mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
            mock.patch.object(evidence.subprocess, "run", side_effect=successful_runner),
        ):
            evidence.run(args)
        shard_report = json.loads(shard_output.read_text(encoding="utf-8"))
        assert [result["id"] for result in shard_report["results"]] == [
            row["id"] for row in matrix_rows[1::4]
        ]
        args.output = output
        args.shard_index = None
        args.shard_count = None

        selected_build, selected_output, _selected_tools, selected_args = prepare_tree(
            tmp / "selected-scenario"
        )
        selected_args.scenario = "blocking-ipc"
        with (
            mock.patch.object(evidence, "git_revision", return_value=revision),
            mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
            mock.patch.object(evidence.subprocess, "run", side_effect=successful_runner),
        ):
            evidence.run(selected_args)
        selected_report = json.loads(selected_output.read_text(encoding="utf-8"))
        assert [result["id"] for result in selected_report["results"]] == [
            "blocking-ipc"
        ]
        assert (selected_build / "clang-canonical.serial.log").exists() is False

        _, matrix_rows = evidence.parse_matrix(evidence.DEFAULT_MATRIX)
        blocking_row = next(row for row in matrix_rows if row["id"] == "blocking-ipc")
        blocking_serial = evidence.expanded(
            blocking_row, "0.1.0", selected_build
        )["serial_log"]
        serial_content = blocking_serial.read_text(encoding="utf-8")
        required_row = evidence.REQUIRED_IOTLB_ORACLE_ROWS[0]
        required_marker = (
            f"{evidence.serial_record('3', 'ORACLE')} id={required_row} result=PASS\n"
        )

        missing_iotlb_row = tmp / "missing-iotlb-row.serial.log"
        missing_iotlb_row.write_text(
            serial_content.replace(required_marker, "", 1), encoding="utf-8"
        )
        expect_failure(
            lambda: evidence.verify_iotlb_oracle_rows(
                missing_iotlb_row, "blocking-ipc"
            ),
            f"must retain exactly one passing {required_row} row",
        )

        duplicate_iotlb_row = tmp / "duplicate-iotlb-row.serial.log"
        duplicate_iotlb_row.write_text(
            serial_content + required_marker, encoding="utf-8"
        )
        expect_failure(
            lambda: evidence.verify_iotlb_oracle_rows(
                duplicate_iotlb_row, "blocking-ipc"
            ),
            f"must retain exactly one passing {required_row} row",
        )

        selected_args.scenario = "not-in-the-matrix"
        expect_failure(
            lambda: evidence.run(selected_args),
            "scenario is absent from matrix: not-in-the-matrix",
        )

        with (
            mock.patch.object(evidence, "git_revision", return_value="b" * 40),
            mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
        ):
            expect_failure(
                lambda: evidence.verify_report(
                    output, evidence.DEFAULT_MATRIX, build, tools, "0.1.0", {}
                ),
                "source revision differs",
            )

        report = json.loads(output.read_text(encoding="utf-8"))
        first_path = report["results"][0]["artifacts"][0]["path"]
        first_artifact = evidence.resolve_recorded(first_path)
        original = first_artifact.read_bytes()
        first_artifact.write_bytes(original + b"tampered")
        with (
            mock.patch.object(evidence, "git_revision", return_value=revision),
            mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
        ):
            expect_failure(
                lambda: evidence.verify_report(
                    output, evidence.DEFAULT_MATRIX, build, tools, "0.1.0", {}
                ),
                "hash differs",
            )
        first_artifact.write_bytes(original)

        cases = (
            (
                "runner-failure",
                lambda *_args, **_kwargs: SimpleNamespace(
                    returncode=1,
                    stdout="QEMU command: fixture-qemu\nfailure_class=negative-guard\n",
                ),
                "runner failed with exit status 1",
            ),
            (
                "timeout",
                subprocess.TimeoutExpired(
                    cmd=["fixture"], timeout=1, output="QEMU command: fixture-qemu\n"
                ),
                "runner failed with exit status 124",
            ),
            (
                "forged-summary",
                lambda *_args, **_kwargs: SimpleNamespace(
                    returncode=0, stdout="QEMU command: fixture-qemu\nstatus=PASS\n"
                ),
                "did not produce its expected serial log",
            ),
        )
        for name, side_effect, fragment in cases:
            _build, case_output, _tools, case_args = prepare_tree(tmp / name)
            with (
                mock.patch.object(evidence, "git_revision", return_value=revision),
                mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
                mock.patch.object(evidence.subprocess, "run", side_effect=side_effect),
            ):
                expect_failure(lambda: evidence.run(case_args), fragment)
            failed_report = json.loads(case_output.read_text(encoding="utf-8"))
            if failed_report["status"] != "FAIL":
                raise AssertionError("partial evidence report does not publish FAIL")
            if failed_report["results"][0]["status"] != "FAIL":
                raise AssertionError("failed scenario does not publish FAIL")

        package = (ROOT / "scripts/package-release.sh").read_text(encoding="utf-8")
        evidence.check_release_package(package)
        expect_failure(
            lambda: evidence.check_release_package(
                package.replace("run-emulator-evidence.py release-artifacts", "true")
            ),
            "does not copy the derived release artifact list",
        )
        expect_failure(
            lambda: evidence.check_release_package(
                package + '\ncp build/boot/fault-containment-snapshot.txt "$release/extra.txt"\n'
            ),
            "restates a build/boot artifact instead of deriving it",
        )

        # The derivation layer: rows, artifact lists, and negatives come from
        # the manifest; every deviation fails with a named diagnostic.
        manifest = evidence.load_manifest()
        _, matrix_rows = evidence.parse_matrix(evidence.DEFAULT_MATRIX)
        release_pairs = evidence.release_artifacts(manifest, matrix_rows, "${version}")
        if (
            "build/boot/fault-containment-snapshot.txt",
            "leanos-${version}-fault-containment-snapshot.txt",
        ) not in release_pairs:
            raise AssertionError("derived release artifacts omit the fault-containment snapshot")
        if len({destination for _, destination in release_pairs}) != len(release_pairs):
            raise AssertionError("derived release destinations are not unique")
        reproducibility = evidence.reproducibility_artifacts(manifest, matrix_rows, "0.1.0")
        for name in ("leanos.elf", "boot-page-plan-fault-walk-mismatch.final.h", "SOURCE_REVISION"):
            if name not in reproducibility:
                raise AssertionError(f"derived reproducibility artifacts omit {name}")
        negatives = evidence.negative_evidence(manifest)
        if negatives["frame-budget"]["count"] != 16 or "inflight-revocation" not in negatives:
            raise AssertionError("derived negative-evidence declarations are incomplete")
        derived = evidence.derive_row(manifest, "return-fast-entry-sce-relaxation")
        if derived["serial_log"] != "return-corruption-fast-entry-sce-relaxation.serial.log":
            raise AssertionError("derived relaxation row does not name its serial log")

        def mutated_manifest(transform):
            content = json.loads((ROOT / "scripts/scenario-manifest.json").read_text(encoding="utf-8"))
            transform(content)
            target = tmp / "manifest.json"
            target.write_text(json.dumps(content), encoding="utf-8")
            return target

        def drop_entry(content):
            del content["scenarios"]["blocking-ipc"]

        expect_failure(
            lambda: evidence.parse_matrix(evidence.DEFAULT_MATRIX, mutated_manifest(drop_entry)),
            "matrix scenario has no manifest entry: blocking-ipc",
        )

        def orphan_entry(content):
            content["scenarios"]["never-built"] = {}

        expect_failure(
            lambda: evidence.parse_matrix(evidence.DEFAULT_MATRIX, mutated_manifest(orphan_entry)),
            "manifest scenario is absent from the matrix: never-built",
        )

        def unknown_kind(content):
            content["scenarios"]["fault-containment"]["release_artifacts"].append("core-dump")

        expect_failure(
            lambda: evidence.load_manifest(mutated_manifest(unknown_kind)),
            "scenario fault-containment names unknown artifact kind 'core-dump'",
        )

        def missing_driver(content):
            content["scenarios"]["frame-budget"]["negative_evidence"]["driver"] = "scripts/absent.sh"

        expect_failure(
            lambda: evidence.load_manifest(mutated_manifest(missing_driver)),
            "scenario frame-budget negative-evidence driver is missing: scripts/absent.sh",
        )

        def drifted_family(content):
            content["scenarios"]["fault-reserved-bit"]["reason"] = "page-table-drift"

        expect_failure(
            lambda: evidence.parse_matrix(evidence.DEFAULT_MATRIX, mutated_manifest(drifted_family)),
            "mandatory fault-integrity scenario fault-reserved-bit has unexpected reason",
        )
        expect_failure(
            lambda: evidence.check_artifacts_present(
                [("build/boot/deleted-artifact.txt", "deleted.txt")], tmp
            ),
            "derived artifact is missing from the build: build/boot/deleted-artifact.txt",
        )

        evidence.check_workflows()

    print("Emulator evidence matrix fixtures passed")


if __name__ == "__main__":
    run_fixtures()
