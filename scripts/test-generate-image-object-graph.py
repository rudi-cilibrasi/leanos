#!/usr/bin/env python3
"""Regression tests for the generated shared image-object graph."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("generate-image-object-graph.py")
BUILD_SCRIPT = Path(__file__).with_name("build-image.sh")
ASSIGNED_EDU_SCRIPT = Path(__file__).with_name("build-assigned-edu-image.sh")
PLAN_SCRIPT = Path(__file__).with_name("generate-boot-page-plan.sh")
CI_WORKFLOW = Path(__file__).parents[1] / ".github" / "workflows" / "ci.yml"
SPEC = importlib.util.spec_from_file_location("image_object_graph", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImageObjectGraphTests(unittest.TestCase):
    def test_serial_graph_parity_excludes_partitioned_intermediate_objects(
        self,
    ) -> None:
        workflow = CI_WORKFLOW.read_text(encoding="utf-8")
        parity_job = workflow.split("  serial-graph-parity:", maxsplit=1)[1]
        self.assertIn("! -name '*.o'", parity_job)
        self.assertIn("! -name 'SHA256SUMS'", parity_job)
        self.assertIn('serial-graph-mismatches.txt', parity_job)
        self.assertIn('serial-graph-first-mismatch', parity_job)
        self.assertIn('first differing bytes (offset serial graph):', parity_job)
        self.assertIn('cmp -l "$first_mismatch_dir/serial-artifact"', parity_job)
        self.assertLess(
            parity_job.index('done < "${RUNNER_TEMP}/serial-artifacts.list"'),
            parity_job.index('serial/graph byte mismatch: SHA256SUMS'),
        )
        self.assertIn("final\n          # deliverable/evidence artifacts", parity_job)

    def test_parity_preserves_phase_timing_evidence(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        workflow = CI_WORKFLOW.read_text(encoding="utf-8")
        parity_job = workflow.split("  serial-graph-parity:", maxsplit=1)[1]
        for phase in (
            "bootstrap-and-lean-generation",
            "object-graph-prelinks",
            "boot-plans-and-final-links",
            "policy-and-fixture-validation",
            "iso-packaging",
            "manifests-and-completion",
        ):
            self.assertIn(f"record_build_phase {phase}", wrapper)
        self.assertIn(
            'LEANOS_BUILD_TIMING_FILE="${RUNNER_TEMP}/graph-build-phases.tsv"',
            parity_job,
        )
        self.assertIn("${{ runner.temp }}/graph-build-phases.tsv", parity_job)

    def test_assigned_edu_cache_is_input_and_output_integrity_bound(self) -> None:
        builder = ASSIGNED_EDU_SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'assigned_cache_signature="$build/assigned-edu.inputs.sha256"',
            builder,
        )
        self.assertIn(
            'assigned_cache_manifest="$build/assigned-edu.outputs.sha256"',
            builder,
        )
        self.assertIn(
            '"$current_lean_c_signature" "$current_graph_signature"', builder
        )
        self.assertIn(
            '"$iso_packaging_signature" "$source_revision" "$version"', builder
        )
        self.assertIn('scripts/build-assigned-edu-image.sh', builder)
        self.assertIn('"$build/FaultDispatch.o")"', builder)
        self.assertIn('sha256sum -c --status "$assigned_cache_manifest"', builder)
        self.assertIn('sha256sum "${assigned_outputs[@]}"', builder)
        self.assertLess(
            builder.index('mv "$assigned_manifest_tmp" "$assigned_cache_manifest"'),
            builder.index(
                "printf '%s\\n' \"$assigned_current_signature\" "
                '> "$assigned_cache_signature"'
            ),
        )

    def test_generate_lean_c_initializes_output_before_staging(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        function = "generate_lean_c() {" + wrapper.split(
            "generate_lean_c() {", 1
        )[1].split("\nlean_c_modules=(", 1)[0]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "input.lean"
            output = root / "output.c"
            source.write_text("generated C\n", encoding="utf-8")
            shell = f"""\
set -euo pipefail
lean_c_stage={root!s}/stage
mkdir -p "$lean_c_stage"
lake() {{
  cp "$4" "${{3#--c=}}"
}}
{function}
generate_lean_c {source!s} {output!s}
"""
            subprocess.run(["bash", "-c", shell], check=True)
            self.assertEqual(output.read_text(encoding="utf-8"), "generated C\n")

    def test_build_wrapper_preserves_graph_owned_outputs(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertNotIn('rm -rf "$build"\n', wrapper)
        self.assertNotIn("-type d -name 'iso*'", wrapper)
        self.assertIn('ensure_boot_plan_stub "$build/boot-page-plan.h"', wrapper)
        self.assertIn('mktemp -d "$build/.lean-c.XXXXXX"', wrapper)
        self.assertIn('graph_signature="$build/generated-image-objects.sha256"', wrapper)
        self.assertIn('signature_file="${output}.inputs.sha256"', wrapper)

    def test_build_wrapper_ignores_timestamp_only_kernel_source_changes(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'kernel_source_signature="$build/kernel-source.inputs.sha256"',
            wrapper,
        )
        self.assertIn(
            'kernel_source_make_args=(-o "$repo_root/boot/kernel.c")', wrapper
        )
        self.assertEqual(
            wrapper.count('"${kernel_source_make_args[@]}"'),
            6,
        )
        self.assertIn(
            '"$current_kernel_source_signature" > "$kernel_source_signature"',
            wrapper,
        )

    def test_build_wrapper_observes_preserved_object_mtimes_before_prelink(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        object_targets = (
            "shared-generated-objects variant-kernel-objects "
            "variant-assembly-objects"
        )
        prelink_targets = (
            "prelink-images policy-fixture-images return-corruption-prelinks"
        )
        self.assertIn(object_targets + "\n    make -f", wrapper)
        self.assertIn(prelink_targets, wrapper)
        self.assertNotIn(object_targets + " \\\n    " + prelink_targets, wrapper)

    def test_build_wrapper_parallelizes_independent_boot_plan_generation(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("run_boot_plan_batch()", wrapper)
        self.assertIn("lake build leanos-boot-plan leanos-vtd-plan", wrapper)
        self.assertIn("export LEANOS_BOOT_PLAN_EXECUTABLES_READY=1", wrapper)
        self.assertIn('xargs -0 -r -n 2 -P "${LEANOS_BUILD_JOBS:-$(nproc)}"', wrapper)
        self.assertIn('run_boot_plan_batch "${boot_plan_batch_args[@]}"', wrapper)
        for stem in (
            "leanos-prelink",
            "leanos-malformed-handoff-prelink",
            "leanos-frame-budget-prelink",
            "leanos-fault-containment-prelink",
            "leanos-fault-readonly-write-prelink",
            "leanos-fault-nx-execute-prelink",
            "leanos-entry-stack-overflow-prelink",
            "leanos-direct-port-serial-prelink",
            "leanos-bootstrap64-nmi-prelink",
        ):
            self.assertIn(f'"$build/{stem}.elf"', wrapper)
        for template in (
            "leanos-extended-state${suffix}-prelink",
            "leanos-fast-entry-${mechanism}-prelink",
            "leanos-direct-port-${probe}-prelink",
            "leanos-return-${fixture}-prelink",
        ):
            self.assertIn(f'"$build/{template}.elf"', wrapper)

        plan_script = PLAN_SCRIPT.read_text(encoding="utf-8")
        self.assertIn('"$root/.lake/build/bin/leanos-boot-plan"', plan_script)
        self.assertIn('"$root/.lake/build/bin/leanos-vtd-plan"', plan_script)

    def test_iso_cache_tracks_staged_bytes_and_packaging_tool(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        packaging = "compute_iso_packaging_signature() {" + wrapper.split(
            "compute_iso_packaging_signature() {", 1
        )[1].split("\n}\niso_packaging_signature=", 1)[0] + "\n}"
        compute = "compute_iso_signature() {" + wrapper.split(
            "compute_iso_signature() {", 1
        )[1].split("\n}\n\n# Preserve a deterministic ISO", 1)[0] + "\n}"
        build = "grub-mkrescue() {" + wrapper.split(
            "grub-mkrescue() {", 1
        )[1].split("\n}\n\nrun_iso_packaging", 1)[0] + "\n}"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            staging = root / "iso"
            (staging / "boot").mkdir(parents=True)
            staged = staging / "boot" / "leanos.elf"
            staged.write_text("first\n", encoding="utf-8")
            tool = root / "grub-mkrescue"
            log = root / "calls"
            tool.write_text(
                "#!/bin/sh\n"
                "if [ \"${1:-}\" = --version ]; then echo grub-test-v1; exit 0; fi\n"
                f"echo call >> {log!s}\n"
                "while [ \"$1\" != -o ]; do shift; done\n"
                "shift\n"
                "printf 'iso\\n' > \"$1\"\n",
                encoding="utf-8",
            )
            tool.chmod(0o755)
            xorriso = root / "xorriso"
            mformat = root / "mformat"
            grub_mkimage = root / "grub-mkimage"
            grub_mkstandalone = root / "grub-mkstandalone"
            for subordinate in (
                xorriso,
                mformat,
                grub_mkimage,
                grub_mkstandalone,
            ):
                subordinate.write_text("tool-v1\n", encoding="utf-8")
            modules = root / "grub-modules"
            modules.mkdir()
            module = modules / "normal.mod"
            module.write_text("module-v1\n", encoding="utf-8")
            output = root / "image.iso"
            shell = f"""\
set -euo pipefail
repo_root={root!s}
grub_mkrescue_path={tool!s}
xorriso_path={xorriso!s}
mformat_path={mformat!s}
grub_mkimage_path={grub_mkimage!s}
grub_mkstandalone_path={grub_mkstandalone!s}
grub_module_root={modules!s}
{packaging}
iso_packaging_signature="$(compute_iso_packaging_signature)"
{compute}
{build}
grub-mkrescue -d /grub -o {output!s} {staging!s} -- -fixed
grub-mkrescue -d /grub -o {output!s} {staging!s} -- -fixed
"""
            subprocess.run(["bash", "-c", shell], check=True)
            self.assertEqual(log.read_text(encoding="utf-8").splitlines(), ["call"])

            staged.write_text("second\n", encoding="utf-8")
            subprocess.run(["bash", "-c", shell], check=True)
            self.assertEqual(
                log.read_text(encoding="utf-8").splitlines(), ["call", "call"]
            )

            xorriso.write_text("tool-v2\n", encoding="utf-8")
            subprocess.run(["bash", "-c", shell], check=True)
            self.assertEqual(
                log.read_text(encoding="utf-8").splitlines(),
                ["call", "call", "call"],
            )

            module.write_text("module-v2\n", encoding="utf-8")
            subprocess.run(["bash", "-c", shell], check=True)
            self.assertEqual(
                log.read_text(encoding="utf-8").splitlines(),
                ["call", "call", "call", "call"],
            )

    def test_iso_family_uses_bounded_parallel_packaging(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("run_iso_packaging() {", wrapper)
        self.assertIn('iso_task_file="$build/iso-packaging-tasks.nul"', wrapper)
        self.assertIn('xargs -0 -r -n 2 -P "$policy_jobs"', wrapper)
        self.assertIn(
            "export -f compute_iso_signature grub-mkrescue run_iso_packaging",
            wrapper,
        )
        for output in (
            "x86_64.iso",
            "x86_64-fault-containment.iso",
            "x86_64-extended-state.iso",
            "x86_64-bootstrap64-nmi.iso",
            "x86_64-direct-port-${probe}.iso",
            "x86_64-return-${fixture}.iso",
        ):
            self.assertIn(output, wrapper)
        self.assertIn(
            'echo "error: one or more deterministic ISO packages failed"', wrapper
        )

    def test_iso_batch_propagates_packager_failure_without_caching(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        compute = "compute_iso_signature() {" + wrapper.split(
            "compute_iso_signature() {", 1
        )[1].split("\n}\n\n# Preserve a deterministic ISO", 1)[0] + "\n}"
        build = "grub-mkrescue() {" + wrapper.split(
            "grub-mkrescue() {", 1
        )[1].split("\n}\n\nrun_iso_packaging", 1)[0] + "\n}"
        run = "run_iso_packaging() {" + wrapper.split(
            "run_iso_packaging() {", 1
        )[1].split("\n}\nexport repo_root", 1)[0] + "\n}"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            staging = root / "iso"
            staging.mkdir()
            (staging / "input").write_text("staged\n", encoding="utf-8")
            output = root / "partial.iso"
            task_file = root / "tasks.nul"
            tool = root / "grub-mkrescue"
            tool.write_text(
                "#!/bin/sh\n"
                "while [ \"$1\" != -o ]; do shift; done\n"
                "shift\n"
                "printf 'partial\\n' > \"$1\"\n"
                "exit 7\n",
                encoding="utf-8",
            )
            tool.chmod(0o755)
            shell = f"""\
set -u
repo_root={root!s}
iso_packaging_signature=test-signature
grub_mkrescue_path={tool!s}
{compute}
{build}
{run}
export repo_root iso_packaging_signature grub_mkrescue_path
export -f compute_iso_signature grub-mkrescue run_iso_packaging
printf '%s\\0%s\\0' {output!s} {staging!s} > {task_file!s}
if xargs -0 -r -n 2 -P 1 bash -c 'run_iso_packaging "$@"' _ < {task_file!s}; then
  exit 99
fi
test ! -e {output!s}
test ! -e {output!s}.inputs.sha256
"""
            subprocess.run(["bash", "-c", shell], check=True)

    def test_image_policy_checks_use_bounded_parallel_batch(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("compute_validation_tool_signature() {", wrapper)
        self.assertIn(
            'signature="$(compute_check_signature image-policy "$elf"', wrapper
        )
        self.assertIn('cached_check_is_current "$log" "$signature"', wrapper)
        self.assertIn('record_check_signature "$log" "$signature"', wrapper)
        self.assertIn('policy_jobs="${LEANOS_BUILD_JOBS:-$(nproc)}"', wrapper)
        self.assertIn('xargs -0 -r -n 4 -P "$policy_jobs"', wrapper)
        self.assertIn('export -f run_image_policy_check', wrapper)
        self.assertIn(
            'queue_image_policy canonical "$build/leanos.elf"', wrapper
        )
        self.assertIn(
            'queue_image_policy bootstrap64-nmi '
            '"$build/leanos-bootstrap64-nmi.elf"',
            wrapper,
        )
        self.assertIn(
            'echo "error: one or more image policy checks failed"', wrapper
        )

    def test_validation_cache_reuses_only_matching_inputs(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        helpers = "compute_check_signature() {" + wrapper.split(
            "compute_check_signature() {", 1
        )[1].split("\ncompute_iso_signature() {", 1)[0]
        image_check = "run_image_policy_check() {" + wrapper.split(
            "run_image_policy_check() {", 1
        )[1].split("\n}\nexport -f run_image_policy_check", 1)[0] + "\n}"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            logs = root / "build" / "image-policy-logs"
            scripts.mkdir()
            logs.mkdir(parents=True)
            counter = root / "calls"
            elf = root / "image.elf"
            elf.write_text("elf-v1\n", encoding="utf-8")
            check = scripts / "check-image-policy.sh"
            check.write_text(
                "#!/bin/sh\n" f"echo call >> {counter!s}\n" "echo policy-ok\n",
                encoding="utf-8",
            )
            check.chmod(0o755)

            def run(signature: str, times: int = 1) -> None:
                calls = "\n".join(
                    f"run_image_policy_check canonical {elf!s} '' ''"
                    for _ in range(times)
                )
                shell = f"""\
set -euo pipefail
cd {root!s}
validation_tool_signature={signature}
build={root!s}/build
{helpers}
{image_check}
{calls}
"""
                subprocess.run(["bash", "-c", shell], check=True)

            run("tools-v1", times=2)
            self.assertEqual(counter.read_text(encoding="utf-8"), "call\n")
            elf.write_text("elf-v2\n", encoding="utf-8")
            run("tools-v1")
            self.assertEqual(counter.read_text(encoding="utf-8"), "call\ncall\n")
            run("tools-v2")
            self.assertEqual(
                counter.read_text(encoding="utf-8"), "call\ncall\ncall\n"
            )

    def test_fixture_suite_cache_reuses_only_matching_inputs(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        helpers = "compute_check_signature() {" + wrapper.split(
            "compute_check_signature() {", 1
        )[1].split("\ncompute_iso_signature() {", 1)[0]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            counter = root / "calls"
            output = root / "fixture.log"
            input_file = root / "image.elf"
            input_file.write_text("elf-v1\n", encoding="utf-8")
            check = root / "fixture-check.sh"
            check.write_text(
                "#!/bin/sh\n" f"echo call >> {counter!s}\n" "echo fixture-ok\n",
                encoding="utf-8",
            )
            check.chmod(0o755)

            def run(signature: str, times: int = 1) -> None:
                calls = "\n".join(
                    f"run_cached_fixture_check {output!s} "
                    f"{check!s} {input_file!s}"
                    for _ in range(times)
                )
                shell = f"""\
set -euo pipefail
validation_tool_signature={signature}
{helpers}
{calls}
"""
                subprocess.run(["bash", "-c", shell], check=True)

            run("tools-v1", times=2)
            self.assertEqual(counter.read_text(encoding="utf-8"), "call\n")
            input_file.write_text("elf-v2\n", encoding="utf-8")
            run("tools-v1")
            self.assertEqual(counter.read_text(encoding="utf-8"), "call\ncall\n")
            run("tools-v2")
            self.assertEqual(
                counter.read_text(encoding="utf-8"), "call\ncall\ncall\n"
            )

    def test_return_corruption_policy_cache_preserves_expected_failures(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        helpers = "compute_check_signature() {" + wrapper.split(
            "compute_check_signature() {", 1
        )[1].split("\ncompute_iso_signature() {", 1)[0]
        policy_check = "run_return_corruption_policy_check() {" + wrapper.split(
            "run_return_corruption_policy_check() {", 1
        )[1].split(
            "\n}\nexport -f run_return_corruption_policy_check", 1
        )[0] + "\n}"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            logs = root / "logs"
            scripts.mkdir()
            logs.mkdir()
            counter = root / "calls"
            positive = root / "positive.elf"
            negative = root / "negative.elf"
            positive.write_text("positive-v1\n", encoding="utf-8")
            negative.write_text("negative-v1\n", encoding="utf-8")
            check = scripts / "check-image-policy.sh"
            check.write_text(
                "#!/bin/sh\n"
                f"echo call >> {counter!s}\n"
                "case $1 in\n"
                "  *negative*) echo expected-diagnostic; exit 1 ;;\n"
                "  *) echo policy-ok ;;\n"
                "esac\n",
                encoding="utf-8",
            )
            check.chmod(0o755)

            def run(
                signature: str, elf: Path, expected: str, times: int = 1
            ) -> None:
                log = logs / f"{elf.stem}.log"
                calls = "\n".join(
                    f"run_return_corruption_policy_check {elf.stem} "
                    f"{elf!s} {expected!r} {log!s}"
                    for _ in range(times)
                )
                shell = f"""\
set -euo pipefail
cd {root!s}
validation_tool_signature={signature}
{helpers}
{policy_check}
{calls}
"""
                subprocess.run(["bash", "-c", shell], check=True)

            run("tools-v1", positive, "", times=2)
            run("tools-v1", negative, "expected-diagnostic", times=2)
            self.assertEqual(counter.read_text(encoding="utf-8"), "call\ncall\n")
            positive.write_text("positive-v2\n", encoding="utf-8")
            run("tools-v1", positive, "")
            run("tools-v2", negative, "expected-diagnostic")
            self.assertEqual(
                counter.read_text(encoding="utf-8"), "call\ncall\ncall\ncall\n"
            )

    def test_entry_policy_checks_use_bounded_parallel_batch(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'signature="$(compute_check_signature entry-policy "$elf"', wrapper
        )
        self.assertIn(
            'cached_check_is_current "$report" "$signature"', wrapper
        )
        self.assertIn('export -f run_entry_policy_check', wrapper)
        self.assertIn('xargs -0 -r -n 5 -P "$policy_jobs"', wrapper)
        self.assertIn(
            'queue_entry_policy canonical "$build/leanos.elf"', wrapper
        )
        self.assertIn(
            'queue_entry_policy "fast-entry-$mechanism"', wrapper
        )
        self.assertIn(
            'queue_entry_policy fault-stale-translation', wrapper
        )
        self.assertIn(
            'echo "error: one or more entry policy checks failed"', wrapper
        )

    def test_direct_port_and_negative_fixtures_use_bounded_batches(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'signature="$(compute_check_signature direct-port "$elf"', wrapper
        )
        self.assertIn(
            'signature="$(compute_check_signature return-fixture "$elf"', wrapper
        )
        self.assertIn("export -f run_direct_port_check", wrapper)
        self.assertIn('xargs -0 -r -n 5 -P "$policy_jobs"', wrapper)
        self.assertIn('direct_port_logs+=("$direct_port_log")', wrapper)
        self.assertIn('cat "$log" >> "$direct_port_report"', wrapper)
        self.assertIn("export -f run_return_fixture_check", wrapper)
        self.assertIn('xargs -0 -r -n 4 -P "$policy_jobs"', wrapper)
        self.assertIn(
            "queue_return_fixture restore "
            "'error: unexpected exact user-return restore sequence'",
            wrapper,
        )
        self.assertIn(
            'echo "error: one or more return-policy negative fixtures failed"',
            wrapper,
        )
        self.assertIn(
            'signature="$(compute_check_signature return-corruption-policy "$elf"',
            wrapper,
        )
        self.assertIn("export -f run_return_corruption_policy_check", wrapper)

    def test_graph_signature_changes_with_tool_identity(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        function = "compute_graph_signature() {" + wrapper.split(
            "compute_graph_signature() {", 1
        )[1].split("\n}\n\nrequire_tool lake", 1)[0] + "\n}"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph = root / "objects.mk"
            graph.write_text("all:\n\t@true\n", encoding="utf-8")
            compiler = root / "cc"
            linker = root / "ld"
            compiler.write_text(
                "#!/bin/sh\necho compiler-v1\n", encoding="utf-8"
            )
            linker.write_text("#!/bin/sh\necho linker-v1\n", encoding="utf-8")
            compiler.chmod(0o755)
            linker.chmod(0o755)

            shell = f"""\
set -euo pipefail
PATH={root!s}:$PATH
{function}
compute_graph_signature {graph!s} {compiler!s}
"""
            first = subprocess.run(
                ["bash", "-c", shell], check=True, capture_output=True, text=True
            ).stdout.strip()
            compiler.write_text(
                "#!/bin/sh\necho compiler-v2\n", encoding="utf-8"
            )
            compiler.chmod(0o755)
            second = subprocess.run(
                ["bash", "-c", shell], check=True, capture_output=True, text=True
            ).stdout.strip()

            self.assertNotEqual(first, second)

    def test_generated_make_cache_tracks_inputs_tools_and_outputs(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        function = "compute_graph_make_input_signature() {" + wrapper.split(
            "compute_graph_make_input_signature() {", 1
        )[1].split("\n}\n\ngraph_make_cache_signature=", 1)[0] + "\n}"
        self.assertIn('sha256sum -c --status "$graph_make_cache_manifest"', wrapper)
        self.assertIn("generated-make.outputs.sha256", wrapper)
        self.assertIn("generated-make.inputs.sha256", wrapper)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "repo"
            build = Path(directory) / "build"
            (root / "boot").mkdir(parents=True)
            (root / "include/leanos").mkdir(parents=True)
            build.mkdir()
            source = root / "boot/kernel.c"
            repository_header = root / "include/leanos/composite-dispatcher.h"
            header = build / "boot-page-plan.h"
            generated = build / "Generated.c"
            source.write_text("int kernel(void) { return 1; }\n", encoding="utf-8")
            repository_header.write_text("/* dispatcher */\n", encoding="utf-8")
            header.write_text("/* plan */\n", encoding="utf-8")
            generated.write_text("int generated(void) { return 1; }\n", encoding="utf-8")

            def signature(tool: str = "tool-a") -> str:
                result = subprocess.run(
                    [
                        "bash",
                        "-c",
                        function + f"\ncompute_graph_make_input_signature {tool}",
                    ],
                    check=True,
                    capture_output=True,
                    text=True,
                    env={**os.environ, "repo_root": str(root), "build": str(build)},
                )
                return result.stdout.strip()

            baseline = signature()
            source.write_text("int kernel(void) { return 2; }\n", encoding="utf-8")
            self.assertNotEqual(baseline, signature())
            source.write_text("int kernel(void) { return 1; }\n", encoding="utf-8")
            repository_header.write_text(
                "/* changed dispatcher */\n", encoding="utf-8"
            )
            self.assertNotEqual(baseline, signature())
            repository_header.write_text("/* dispatcher */\n", encoding="utf-8")
            header.write_text("/* changed plan */\n", encoding="utf-8")
            self.assertNotEqual(baseline, signature())
            header.write_text("/* plan */\n", encoding="utf-8")
            generated.write_text("int generated(void) { return 2; }\n", encoding="utf-8")
            self.assertNotEqual(baseline, signature())
            generated.write_text("int generated(void) { return 1; }\n", encoding="utf-8")
            self.assertNotEqual(baseline, signature("tool-b"))

            output = build / "kernel.o"
            output.write_bytes(b"object-a")
            manifest = build / "generated-make.outputs.sha256"
            manifest.write_text(
                subprocess.run(
                    ["sha256sum", str(output)],
                    check=True,
                    capture_output=True,
                    text=True,
                ).stdout,
                encoding="utf-8",
            )
            subprocess.run(
                ["sha256sum", "-c", "--status", str(manifest)], check=True
            )
            output.write_bytes(b"object-b")
            self.assertNotEqual(
                subprocess.run(
                    ["sha256sum", "-c", "--status", str(manifest)]
                ).returncode,
                0,
            )

    def test_lean_c_signature_tracks_sources_and_toolchain(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        function = "compute_lean_c_signature() {" + wrapper.split(
            "compute_lean_c_signature() {", 1
        )[1].split("\n}\n\nrequire_tool lake", 1)[0] + "\n}"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "LeanOS").mkdir()
            source = root / "LeanOS/KernelTransition.lean"
            source.write_text("def generated := 1\n", encoding="utf-8")
            lakefile = root / "lakefile.toml"
            lakefile.write_text(
                'name = "LeanOS"\n', encoding="utf-8"
            )
            tools = root / "tools"
            tools.mkdir()
            lake = tools / "lake"
            lake.write_text(
                "#!/bin/sh\n"
                'if [ "$2" = sh ]; then echo "$0"; else '
                "echo Lean version 4.24.0; fi\n",
                encoding="utf-8",
            )
            lake.chmod(0o755)
            shell = f"""\
set -euo pipefail
PATH={tools!s}:$PATH
{function}
compute_lean_c_signature {root!s}
"""
            first = subprocess.run(
                ["bash", "-c", shell], check=True, capture_output=True, text=True
            ).stdout.strip()
            source.write_text("def generated := 2\n", encoding="utf-8")
            second = subprocess.run(
                ["bash", "-c", shell], check=True, capture_output=True, text=True
            ).stdout.strip()
            lakefile.write_text(
                'name = "LeanOS"\ndefaultTargets = ["kernel"]\n',
                encoding="utf-8",
            )
            third = subprocess.run(
                ["bash", "-c", shell], check=True, capture_output=True, text=True
            ).stdout.strip()
            lake.write_text(
                "#!/bin/sh\n"
                'if [ "$2" = sh ]; then echo "$0"; else '
                "echo Lean version 4.25.0; fi\n",
                encoding="utf-8",
            )
            lake.chmod(0o755)
            fourth = subprocess.run(
                ["bash", "-c", shell], check=True, capture_output=True, text=True
            ).stdout.strip()

            self.assertNotEqual(first, second)
            self.assertNotEqual(second, third)
            self.assertNotEqual(third, fourth)

    def test_build_wrapper_reuses_complete_matching_lean_c_set(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        self.assertIn('lean_c_signature="$build/generated-lean-c.sha256"', wrapper)
        self.assertIn('[[ -f "$build/$module.c" ]] || reuse_lean_c=0', wrapper)
        self.assertIn('if ((reuse_lean_c == 0)); then', wrapper)

    def test_oracle_cache_tracks_inputs_revision_and_output_integrity(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        oracle = BUILD_SCRIPT.with_name("generate-oracle.sh").read_text(
            encoding="utf-8"
        )

        self.assertIn(
            'LEANOS_ORACLE_TOOL_SIGNATURE="$current_lean_c_signature"', wrapper
        )
        self.assertIn('printf \'%s\\0%s\\0\' "$revision" "$tool_signature"', oracle)
        self.assertIn('sha256sum "$root/scripts/generate-oracle.sh"', oracle)
        self.assertIn('stored_tsv_hash', oracle)
        self.assertIn('stored_header_hash', oracle)

    def test_stub_plan_generation_preserves_unchanged_timestamp(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "plan.h"
            subprocess.run(
                [str(PLAN_SCRIPT), "--stub", str(output)], check=True
            )
            fixed_timestamp = 1_700_000_000_000_000_000
            os.utime(output, ns=(fixed_timestamp, fixed_timestamp))
            subprocess.run(
                [str(PLAN_SCRIPT), "--stub", str(output)], check=True
            )
            self.assertEqual(output.stat().st_mtime_ns, fixed_timestamp)

    def test_wrapper_reuses_content_identical_boot_plans(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        plan_script = PLAN_SCRIPT.read_text(encoding="utf-8")

        self.assertIn(
            'export LEANOS_BOOT_PLAN_TOOL_SIGNATURE="$current_lean_c_signature"',
            wrapper,
        )
        self.assertIn('sha256sum "$elf"', plan_script)
        self.assertIn('"$root/scripts/generate-boot-page-plan.sh"', plan_script)
        self.assertIn('printf \'%s\\n\' "$assigned_edu" "$tool_signature"', plan_script)
        self.assertIn('[[ "$stored_signature" == "$signature" ]]', plan_script)
        self.assertIn(
            '[[ "$current_output_hash" == "$stored_output_hash" ]]', plan_script
        )

    def test_bootstrap64_plan_converges_through_graph_target(self) -> None:
        wrapper = BUILD_SCRIPT.read_text(encoding="utf-8")
        function = "converge_selected_graph_plan() {" + wrapper.split(
            "converge_selected_graph_plan() {", 1
        )[1].split("\n}\n\nvalidate_selected_final_plan", 1)[0] + "\n}"

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            generator = scripts / "generate-boot-page-plan.sh"
            generator.write_text('#!/bin/sh\ncp "$1" "$2"\n', encoding="utf-8")
            generator.chmod(0o755)
            expected = root / "plan.h"
            final = root / "plan.final.h"
            elf = root / "image.elf"
            graph = root / "graph.mk"
            expected.write_text("prelink-plan\n", encoding="utf-8")
            elf.write_text("linker-resolved-plan\n", encoding="utf-8")
            graph.write_text(
                f".PHONY: {elf!s}\n"
                f"{elf!s}: {expected!s}\n"
                f"\tcp {expected!s} {elf!s}\n",
                encoding="utf-8",
            )
            shell = f"""\
set -euo pipefail
object_graph={graph!s}
kernel_source_make_args=()
LEANOS_BUILD_JOBS=1
selected_final_enabled() {{ return 0; }}
{function}
converge_selected_graph_plan {elf!s} {expected!s} {final!s} fixture
"""
            subprocess.run(["bash", "-c", shell], check=True, cwd=root)
            self.assertEqual(
                expected.read_text(encoding="utf-8"), "linker-resolved-plan\n"
            )
            self.assertEqual(final.read_bytes(), expected.read_bytes())

    def test_boot_plan_cache_is_per_input_stage_and_checks_output(self) -> None:
        plan_script = PLAN_SCRIPT.read_text(encoding="utf-8")
        symbol_block = plan_script.split("symbols=(", 1)[1].split("\n)", 1)[0]
        vtd_symbol_block = plan_script.split("vtd_symbols=(", 1)[1].split(
            "\n)", 1
        )[0]
        symbols = sorted(set((symbol_block + vtd_symbol_block).split()))

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = root / "tools"
            tools.mkdir()
            nm = tools / "nm"
            nm.write_text(
                "#!/bin/sh\n"
                + "\n".join(
                    f"printf '%08x T {symbol}\\n' {index + 1}"
                    for index, symbol in enumerate(symbols)
                )
                + "\n",
                encoding="utf-8",
            )
            nm.chmod(0o755)
            lake = tools / "lake"
            lake.write_text(
                "#!/bin/sh\n"
                'printf "%s\\n" "$*" >> "$LAKE_LOG"\n'
                'printf "generated-%s\\n" "$3"\n',
                encoding="utf-8",
            )
            lake.chmod(0o755)

            prelink = root / "image-prelink.elf"
            final = root / "image.elf"
            prelink.write_text("prelink input\n", encoding="utf-8")
            final.write_text("final input\n", encoding="utf-8")
            destination = root / "boot-page-plan.h"
            log = root / "lake.log"
            env = {
                **os.environ,
                "PATH": f"{tools!s}:{os.environ['PATH']}",
                "LAKE_LOG": str(log),
                "LEANOS_BOOT_PLAN_TOOL_SIGNATURE": "test-tool-signature",
            }

            for _ in range(2):
                subprocess.run(
                    [str(PLAN_SCRIPT), str(prelink), str(destination)],
                    check=True,
                    env=env,
                )
                subprocess.run(
                    [str(PLAN_SCRIPT), str(final), str(destination)],
                    check=True,
                    env=env,
                )

            self.assertEqual(len(log.read_text(encoding="utf-8").splitlines()), 4)
            self.assertEqual(
                len(list(root.glob("boot-page-plan.h.inputs.*.sha256"))), 2
            )
            expected = destination.read_text(encoding="utf-8")

            destination.write_text("corrupt cached output\n", encoding="utf-8")
            subprocess.run(
                [str(PLAN_SCRIPT), str(prelink), str(destination)],
                check=True,
                env=env,
            )

            self.assertEqual(len(log.read_text(encoding="utf-8").splitlines()), 6)
            self.assertEqual(destination.read_text(encoding="utf-8"), expected)

    def test_graph_compiles_every_generated_module_once(self) -> None:
        graph = MODULE.render_graph(
            Path("build/boot"), "clang-18", ["-m64", "-DVALUE=two words"],
            Path("/lean"), Path("/src")
        )

        for module in MODULE.GENERATED_MODULES:
            self.assertEqual(graph.count(f"/{module}.c"), 1)
        self.assertIn("IMAGE_CC := clang-18", graph)
        self.assertIn("'-DVALUE=two words'", graph)
        self.assertIn("-I/lean/include", graph)

    def test_combined_outputs_depend_on_reviewed_parts(self) -> None:
        graph = MODULE.render_graph(
            Path("out"), "gcc", [], Path("/lean"), Path("/src")
        )

        boot_rule = next(
            line for line in graph.splitlines() if line.startswith("out/BootAllocation.o:")
        )
        fault_rule = next(
            line for line in graph.splitlines() if line.startswith("out/FaultDispatch.o:")
        )
        for module in MODULE.BOOT_ALLOCATION_PARTS:
            self.assertIn(f"out/{module}.part.o", boot_rule)
        for module in MODULE.FAULT_DISPATCH_PARTS:
            self.assertIn(f"out/{module}.part.o", fault_rule)

    def test_cli_writes_deterministic_graph(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "objects.mk"
            first = MODULE.render_graph(
                Path(directory), "gcc", ["-O2"], Path("/lean"), Path("/src")
            )
            output.write_text(first, encoding="utf-8")
            second = MODULE.render_graph(
                Path(directory), "gcc", ["-O2"], Path("/lean"), Path("/src")
            )
            self.assertEqual(output.read_text(encoding="utf-8"), second)

    def test_generated_graph_builds_and_is_incremental(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory) / "build"
            build.mkdir()
            source = Path(directory) / "source"
            (source / "boot").mkdir(parents=True)
            header = source / "boot/test-header.h"
            header.write_text("#define TEST_VALUE 0\n", encoding="utf-8")
            (source / "boot/kernel.c").write_text(
                '#include "test-header.h"\n'
                "int kernel_variant(void) { return TEST_VALUE; }\n",
                encoding="utf-8",
            )
            (source / "boot/boot.S").write_text(".text\n", encoding="utf-8")
            (source / "boot/peer-pke-fixture.S").write_text(
                ".text\n", encoding="utf-8"
            )
            (source / "boot/linker.ld").write_text(
                "SECTIONS { . = 0x100000; .text : { *(.text*) } }\n",
                encoding="utf-8",
            )
            for index, module in enumerate(MODULE.GENERATED_MODULES):
                (build / f"{module}.c").write_text(
                    f"int generated_module_{index}(void) {{ return {index}; }}\n",
                    encoding="utf-8",
                )
            graph = Path(directory) / "objects.mk"
            graph.write_text(
                MODULE.render_graph(
                    build, "gcc", ["-O2"], Path("/lean"), source,
                    [("kernel-selector", 1), ("post-validation-mutation", 11)],
                ),
                encoding="utf-8",
            )
            for fixture in ("kernel-selector", "post-validation-mutation"):
                (build / f"boot-page-plan-return-{fixture}.h").write_text(
                    "/* test plan */\n", encoding="utf-8"
                )

            subprocess.run(
                [
                    "make", "-f", str(graph), "-j2",
                    "shared-generated-objects", "variant-kernel-objects",
                    "variant-assembly-objects", "prelink-images",
                    "policy-fixture-images", "return-corruption-prelinks",
                    "final-image-links", "return-corruption-final-images",
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            self.assertTrue((build / "BootAllocation.o").is_file())
            self.assertTrue((build / "FaultDispatch.o").is_file())
            for name, _ in MODULE.KERNEL_VARIANTS:
                self.assertTrue((build / f"{name}.o").is_file())
            for name, _, _ in MODULE.ASSEMBLY_VARIANTS:
                self.assertTrue((build / f"{name}.o").is_file())
            for name, _, _, _ in MODULE.PRELINK_VARIANTS:
                stem = f"leanos-{name}" if name else "leanos"
                self.assertTrue((build / f"{stem}-prelink.elf").is_file())
                self.assertTrue((build / f"{stem}-prelink.map").is_file())
            for name, _, _, _ in MODULE.POLICY_FIXTURE_VARIANTS:
                self.assertTrue((build / f"leanos-{name}.elf").is_file())
                self.assertTrue((build / f"leanos-{name}.map").is_file())
            for name, _, _, _ in MODULE.FINAL_LINK_VARIANTS:
                stem = f"leanos-{name}" if name else "leanos"
                self.assertTrue((build / f"{stem}.elf").is_file())
                self.assertTrue((build / f"{stem}.map").is_file())
            for fixture in ("kernel-selector", "post-validation-mutation"):
                self.assertTrue((build / f"kernel-return-{fixture}.o").is_file())
                self.assertTrue(
                    (build / f"kernel-return-{fixture}-prelink.o").is_file()
                )
                self.assertTrue(
                    (build / f"leanos-return-{fixture}-prelink.elf").is_file()
                )
                self.assertTrue(
                    (build / f"leanos-return-{fixture}.elf").is_file()
                )
            subprocess.run(
                [
                    "make", "-f", str(graph), "-q",
                    "shared-generated-objects", "variant-kernel-objects",
                    "variant-assembly-objects", "prelink-images",
                    "policy-fixture-images", "return-corruption-prelinks",
                    "final-kernel-objects", "final-image-links",
                    "return-corruption-final-images",
                ],
                check=True,
            )

            # A timestamp-only source touch must not cascade into relinking
            # byte-identical objects and every downstream image artifact.
            kernel_object = build / "kernel.o"
            original_kernel_object = kernel_object.read_bytes()
            original_kernel_mtime = kernel_object.stat().st_mtime_ns
            kernel_source = source / "boot/kernel.c"
            os.utime(
                kernel_source,
                ns=(
                    kernel_source.stat().st_atime_ns,
                    original_kernel_mtime + 1_000_000_000,
                ),
            )
            subprocess.run(
                ["make", "-f", str(graph), "-j2", str(kernel_object)],
                check=True,
                capture_output=True,
                text=True,
            )
            self.assertEqual(kernel_object.read_bytes(), original_kernel_object)
            self.assertEqual(kernel_object.stat().st_mtime_ns, original_kernel_mtime)

            # A retained object without its compiler dependency file is not a
            # trustworthy cache entry: the graph must rebuild it before a
            # changed included header can be hidden from Make.
            (build / "kernel.o.d").unlink()
            header.write_text("#define TEST_VALUE 1\n", encoding="utf-8")
            subprocess.run(
                ["make", "-f", str(graph), "-j2", str(kernel_object)],
                check=True,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(kernel_object.read_bytes(), original_kernel_object)

    def test_kernel_variant_flags_are_owned_by_the_graph(self) -> None:
        graph = MODULE.render_graph(
            Path("out"), "gcc", ["-O2"], Path("/lean"), Path("/src")
        )
        graph_lines = graph.splitlines()
        self.assertIn("out/kernel-preemption.o out/kernel-preemption.o.d &:", graph)
        self.assertIn("-DLEANOS_PREEMPTION_SCENARIO=1", graph)
        self.assertIn(
            "out/kernel-fault-stale-translation.o "
            "out/kernel-fault-stale-translation.o.d &:",
            graph,
        )
        self.assertIn("boot-page-plan-fault-stale-translation.h", graph)
        for variant, plan in (
            ("kernel-fault-reserved-bit", "boot-page-plan-fault-reserved-bit.h"),
            ("kernel-fault-walk-mismatch", "boot-page-plan-fault-walk-mismatch.h"),
        ):
            command = next(
                graph_lines[index + 1]
                for index, line in enumerate(graph_lines)
                if line.startswith(f"out/{variant}.o out/{variant}.o.d &:")
            )
            self.assertIn(f'BOOT_PAGE_PLAN_HEADER="{plan}"', command)
        self.assertIn(
            "out/kernel-entry-stack-overflow.o "
            "out/kernel-entry-stack-overflow.o.d &:",
            graph,
        )
        self.assertIn("boot-page-plan-entry-overflow.h", graph)
        for variant, plan in (
            ("kernel-nmi", "boot-page-plan-nmi.h"),
            ("kernel-bootstrap32-ud", "boot-page-plan-bootstrap32-ud.h"),
            ("kernel-bootstrap64-nmi", "boot-page-plan-bootstrap64-nmi.h"),
        ):
            command = next(
                graph_lines[index + 1]
                for index, line in enumerate(graph_lines)
                if line.startswith(f"out/{variant}.o out/{variant}.o.d &:")
            )
            self.assertIn(f'BOOT_PAGE_PLAN_HEADER="{plan}"', command)
        self.assertIn("variant-kernel-objects:", graph)
        self.assertIn("final-kernel-objects:", graph)

    def test_assembly_variant_flags_are_owned_by_the_graph(self) -> None:
        graph = MODULE.render_graph(
            Path("out"), "gcc", ["-O2"], Path("/lean"), Path("/src")
        )
        self.assertIn(
            "out/boot-fault-reserved-bit.o out/boot-fault-reserved-bit.o.d &:",
            graph,
        )
        self.assertIn("-DLEANOS_PAGE_FAULT_PROBE_RESERVED_BIT=1", graph)
        self.assertIn(
            "out/boot-direct-port-pic.o out/boot-direct-port-pic.o.d &:", graph
        )
        self.assertIn("-DLEANOS_DIRECT_PORT_PROBE_PIC=1", graph)
        self.assertIn(
            "out/peer-pke-fixture.o out/peer-pke-fixture.o.d &: "
            "/src/boot/peer-pke-fixture.S",
            graph,
        )

    def test_prelink_rules_preserve_input_order_and_map_outputs(self) -> None:
        graph = MODULE.render_graph(
            Path("out"), "gcc", ["-O2"], Path("/lean"), Path("/src")
        )
        rule = next(
            line
            for line in graph.splitlines()
            if line.startswith("out/leanos-prelink.elf:")
        )
        self.assertLess(rule.index("out/boot.o"), rule.index("out/kernel.o"))
        self.assertLess(
            rule.index("out/kernel.o"), rule.index("out/KernelTransition.o")
        )
        self.assertIn("-Map out/leanos-prelink.map", graph)
        self.assertIn(
            "out/leanos-raw-selection-authority-mutation-prelink.elf:", graph
        )
        self.assertIn("out/leanos-preemption-prelink.elf:", graph)
        self.assertIn("out/leanos-fault-readonly-write-prelink.elf:", graph)
        self.assertIn("out/leanos-fault-stale-translation-prelink.elf:", graph)
        peer_rule = next(
            line
            for line in graph.splitlines()
            if line.startswith("out/leanos-extended-state-peer-pke-prelink.elf:")
        )
        self.assertLess(
            peer_rule.index("out/boot-extended-state-peer-pke.o"),
            peer_rule.index("out/peer-pke-fixture.o"),
        )
        self.assertLess(
            peer_rule.index("out/peer-pke-fixture.o"),
            peer_rule.index("out/kernel-extended-state-peer-pke.o"),
        )
        self.assertIn("out/leanos-extended-state-avx-prelink.elf:", graph)
        self.assertIn("out/leanos-fast-entry-syscall-prelink.elf:", graph)
        self.assertIn("out/leanos-fast-entry-sysenter-prelink.elf:", graph)
        self.assertIn("out/leanos-double-fault-prelink.elf:", graph)
        self.assertIn("out/leanos-entry-stack-overflow-prelink.elf:", graph)
        self.assertIn("out/leanos-entry-adversarial-prelink.elf:", graph)
        self.assertIn("out/leanos-direct-port-pic-prelink.elf:", graph)
        self.assertIn("out/leanos-divide-error-prelink.elf:", graph)
        self.assertIn("out/leanos-breakpoint-prelink.elf:", graph)
        self.assertIn("out/leanos-nmi-prelink.elf:", graph)
        self.assertIn("out/leanos-bootstrap32-ud-prelink.elf:", graph)
        self.assertIn("out/leanos-bootstrap64-nmi-prelink.elf:", graph)
        self.assertIn("out/leanos-guard-prelink.elf:", graph)
        self.assertIn("out/leanos.elf:", graph)
        self.assertIn("out/leanos-fast-entry-sysenter.elf:", graph)
        self.assertNotIn("out/leanos-double-fault.elf:", graph)
        fixture_rule = next(
            line
            for line in graph.splitlines()
            if line.startswith("out/leanos-return-restore-fixture.elf:")
        )
        self.assertLess(
            fixture_rule.index("out/boot-return-restore-fixture.o"),
            fixture_rule.index("out/kernel.o"),
        )
        self.assertIn(
            "-Map out/leanos-return-initial-indirect-fixture.map", graph
        )

    def test_return_corruption_graph_preserves_matrix_mapping(self) -> None:
        graph = MODULE.render_graph(
            Path("out"), "gcc", ["-O2"], Path("/lean"), Path("/src"),
            [("kernel-selector", 1), ("post-validation-mutation", 11)],
        )
        self.assertIn(
            "out/kernel-return-kernel-selector-prelink.o "
            "out/kernel-return-kernel-selector-prelink.o.d &:",
            graph,
        )
        self.assertIn(
            "out/kernel-return-kernel-selector.o "
            "out/kernel-return-kernel-selector.o.d &:",
            graph,
        )
        self.assertIn("-DLEANOS_RETURN_CORRUPTION_MODE=1", graph)
        regular_rule = next(
            line for line in graph.splitlines()
            if line.startswith("out/leanos-return-kernel-selector-prelink.elf:")
        )
        self.assertIn("out/boot.o", regular_rule)
        self.assertIn("out/kernel-return-kernel-selector-prelink.o", regular_rule)
        final_rule = next(
            line for line in graph.splitlines()
            if line.startswith("out/leanos-return-kernel-selector.elf:")
        )
        self.assertIn("out/kernel-return-kernel-selector.o", final_rule)
        post_validation_rule = next(
            line for line in graph.splitlines()
            if line.startswith(
                "out/leanos-return-post-validation-mutation-prelink.elf:"
            )
        )
        self.assertIn("out/boot-return-post-validation-qemu.o", post_validation_rule)

    def test_return_corruption_cli_specs_fail_closed(self) -> None:
        self.assertEqual(
            MODULE.parse_return_corruptions(["kernel-selector:1"]),
            [("kernel-selector", 1)],
        )
        with self.assertRaises(ValueError):
            MODULE.parse_return_corruptions(["missing-mode"])


if __name__ == "__main__":
    unittest.main()
