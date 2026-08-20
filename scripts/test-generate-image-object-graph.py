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
PLAN_SCRIPT = Path(__file__).with_name("generate-boot-page-plan.sh")
SPEC = importlib.util.spec_from_file_location("image_object_graph", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImageObjectGraphTests(unittest.TestCase):
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
        self.assertIn('ensure_boot_plan_stub "$build/boot-page-plan.h"', wrapper)
        self.assertIn('mktemp -d "$build/.lean-c.XXXXXX"', wrapper)
        self.assertIn('graph_signature="$build/generated-image-objects.sha256"', wrapper)

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
            (source / "boot/kernel.c").write_text(
                "int kernel_variant(void) { return 0; }\n", encoding="utf-8"
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

    def test_kernel_variant_flags_are_owned_by_the_graph(self) -> None:
        graph = MODULE.render_graph(
            Path("out"), "gcc", ["-O2"], Path("/lean"), Path("/src")
        )
        self.assertIn("out/kernel-preemption.o:", graph)
        self.assertIn("-DLEANOS_PREEMPTION_SCENARIO=1", graph)
        self.assertIn("out/kernel-fault-stale-translation.o:", graph)
        self.assertIn("boot-page-plan-fault-stale-translation.h", graph)
        self.assertIn("out/kernel-entry-stack-overflow.o:", graph)
        self.assertIn("boot-page-plan-entry-overflow.h", graph)
        self.assertIn("variant-kernel-objects:", graph)
        self.assertIn("final-kernel-objects:", graph)

    def test_assembly_variant_flags_are_owned_by_the_graph(self) -> None:
        graph = MODULE.render_graph(
            Path("out"), "gcc", ["-O2"], Path("/lean"), Path("/src")
        )
        self.assertIn("out/boot-fault-reserved-bit.o:", graph)
        self.assertIn("-DLEANOS_PAGE_FAULT_PROBE_RESERVED_BIT=1", graph)
        self.assertIn("out/boot-direct-port-pic.o:", graph)
        self.assertIn("-DLEANOS_DIRECT_PORT_PROBE_PIC=1", graph)
        self.assertIn("out/peer-pke-fixture.o: /src/boot/peer-pke-fixture.S", graph)

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
        self.assertIn("out/kernel-return-kernel-selector-prelink.o:", graph)
        self.assertIn("out/kernel-return-kernel-selector.o:", graph)
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
