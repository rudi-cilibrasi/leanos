#!/usr/bin/env python3
"""Regression tests for the generated shared image-object graph."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("generate-image-object-graph.py")
SPEC = importlib.util.spec_from_file_location("image_object_graph", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImageObjectGraphTests(unittest.TestCase):
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

            subprocess.run(
                [
                    "make", "-f", str(graph), "-j2",
                    "shared-generated-objects", "variant-kernel-objects",
                    "variant-assembly-objects", "prelink-images",
                    "policy-fixture-images", "return-corruption-prelinks",
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
            for fixture in ("kernel-selector", "post-validation-mutation"):
                self.assertTrue((build / f"kernel-return-{fixture}.o").is_file())
                self.assertTrue(
                    (build / f"leanos-return-{fixture}-prelink.elf").is_file()
                )
            subprocess.run(
                [
                    "make", "-f", str(graph), "-q",
                    "shared-generated-objects", "variant-kernel-objects",
                    "variant-assembly-objects", "prelink-images",
                    "policy-fixture-images", "return-corruption-prelinks",
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
        self.assertIn("out/kernel-return-kernel-selector.o:", graph)
        self.assertIn("-DLEANOS_RETURN_CORRUPTION_MODE=1", graph)
        regular_rule = next(
            line for line in graph.splitlines()
            if line.startswith("out/leanos-return-kernel-selector-prelink.elf:")
        )
        self.assertIn("out/boot.o", regular_rule)
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
