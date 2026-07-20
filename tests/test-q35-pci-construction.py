#!/usr/bin/env python3
"""Negative regressions for the finite q35 construction inventory."""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "scripts" / "check-q35-pci-construction.py"
SPEC = importlib.util.spec_from_file_location("leanos_q35_pci_construction", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
construction = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = construction
SPEC.loader.exec_module(construction)


def accepted_functions() -> list[construction.Function]:
    return [
        construction.Function(bus, device, function, vendor, product, class_code, 0,
                              multifunction)
        for (bus, device, function),
            (vendor, product, class_code, multifunction) in construction.EXPECTED.items()
    ]


class ConstructionValidationTests(unittest.TestCase):
    def assert_rejected(self, functions: list[construction.Function], message: str) -> None:
        with self.assertRaisesRegex(RuntimeError, message):
            construction.validate(functions)

    def test_accepts_exact_quarantined_inventory(self) -> None:
        construction.validate(accepted_functions())

    def test_rejects_duplicate_bdf(self) -> None:
        functions = accepted_functions()
        self.assert_rejected(functions + [functions[0]], "duplicate q35 functions")

    def test_rejects_missing_function(self) -> None:
        self.assert_rejected(accepted_functions()[1:], "q35 inventory mismatch")

    def test_rejects_extra_function(self) -> None:
        functions = accepted_functions()
        functions.append(construction.Function(0, 2, 0, 0xFFFF, 0xFFFF, 0xFFFFFF, 0, False))
        self.assert_rejected(functions, "q35 inventory mismatch")

    def test_rejects_identity_drift(self) -> None:
        functions = accepted_functions()
        original = functions[1]
        functions[1] = construction.Function(
            original.bus, original.device, original.function, original.vendor,
            original.product, original.class_code ^ 1, original.command,
            original.multifunction,
        )
        self.assert_rejected(functions, "identity mismatch")

    def test_rejects_bus_master_readback(self) -> None:
        functions = accepted_functions()
        original = functions[4]
        functions[4] = construction.Function(
            original.bus, original.device, original.function, original.vendor,
            original.product, original.class_code,
            original.command | construction.BUS_MASTER, original.multifunction,
        )
        self.assert_rejected(functions, "bus mastering enabled")


if __name__ == "__main__":
    unittest.main()
