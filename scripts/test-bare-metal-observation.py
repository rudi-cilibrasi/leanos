#!/usr/bin/env python3
"""Controlled fixtures for bare-metal observation metadata validation."""

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("check-bare-metal-observation.py")
SPEC = importlib.util.spec_from_file_location("bare_metal_observation", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
SCHEMA = Path(__file__).resolve().parents[1] / "docs" / "bare-metal-observation.schema.json"


class BareMetalObservationTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.path = Path(self.temp.name) / "observation.json"
        self.value = {
            "schemaVersion": 1,
            "operatorId": "operator-fixture-a",
            "startedAtUtc": "2026-09-09T12:00:00Z",
            "endedAtUtc": "2026-09-09T12:01:00Z",
            "captureCommand": "fixture-capture --timeout 60",
            "captureToolVersion": "fixture-capture 1.0",
            "serialDevice": "/dev/fixture-uart",
            "timeoutSeconds": 60,
            "firmwareSettings": "legacy BIOS; COM1 enabled",
            "pciInventory": "00:00.0 fixture bridge",
            "redactionNote": "fixture identifiers only",
            "resetResult": "halt observed until manual reset",
        }

    def tearDown(self):
        self.temp.cleanup()

    def validate(self):
        self.path.write_text(json.dumps(self.value), encoding="utf-8")
        MODULE.validate(self.path, SCHEMA)

    def test_accepts_bounded_observation(self):
        self.validate()

    def test_rejects_unexpected_metadata(self):
        self.value["hostname"] = "must-not-be-retained"
        with self.assertRaisesRegex(ValueError, "unexpected fields: hostname"):
            self.validate()

    def test_rejects_non_utc_timestamp(self):
        self.value["startedAtUtc"] = "2026-09-09T12:00:00+01:00"
        with self.assertRaisesRegex(ValueError, "expected UTC RFC3339"):
            self.validate()

    def test_rejects_reversed_timestamp_range(self):
        self.value["endedAtUtc"] = "2026-09-09T11:59:59Z"
        with self.assertRaisesRegex(ValueError, "precedes startedAtUtc"):
            self.validate()


if __name__ == "__main__":
    unittest.main()
