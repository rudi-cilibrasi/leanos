#!/usr/bin/env python3
"""Controlled fixtures for the bare-metal rejection classifier."""

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("check-bare-metal-rejection.py")
SPEC = importlib.util.spec_from_file_location("bare_metal_rejection", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
PROTOCOL_PREFIX = "LEANOS" + "/"


class BareMetalRejectionTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.iso = self.root / "image.iso"
        self.elf = self.root / "kernel.elf"
        self.capture = self.root / "serial.log"
        self.manifest = self.root / "machine.json"
        self.iso.write_bytes(b"iso")
        self.elf.write_bytes(b"elf")
        self.revision = "1" * 40
        self.terminal = "LEANOS/1 BOOTALLOC status=FAIL reason=platform-inventory"
        self.write_manifest()

    def tearDown(self):
        self.temp.cleanup()

    def write_manifest(self, **overrides):
        value = {
            "schemaVersion": 1,
            "sourceRevision": self.revision,
            "isoSha256": hashlib.sha256(self.iso.read_bytes()).hexdigest(),
            "elfSha256": hashlib.sha256(self.elf.read_bytes()).hexdigest(),
            "expectedPrefix": ["LEANOS/1 SERIAL status=READY"],
            "expectedTerminal": self.terminal,
            "machine": {
                "model": "fixture-board-rev-a", "cpu": "fixture-x86-64",
                "firmware": "fixture-bios-1", "uart": "COM1 115200 8N1",
                "captureAdapter": "fixture-usb-uart",
            },
        }
        value.update(overrides)
        self.manifest.write_text(json.dumps(value), encoding="utf-8")

    def classify(self, text, **kwargs):
        self.capture.write_bytes(text)
        return MODULE.classify(self.manifest, self.iso, self.elf, self.capture,
                               kwargs.get("revision", self.revision))

    def assert_result(self, result, text, **kwargs):
        with self.assertRaises(MODULE.ClassificationError) as caught:
            self.classify(text, **kwargs)
        self.assertEqual(caught.exception.result, result)

    def test_accepts_exact_final_rejection_and_binds_evidence(self):
        result = self.classify(("LEANOS/1 SERIAL status=READY\r\n" + self.terminal + "\r\n").encode())
        self.assertEqual(result["result"], "exact-typed-rejection")
        self.assertEqual(result["captureBytes"], self.capture.stat().st_size)
        self.assertEqual(result["machine"]["model"], "fixture-board-rev-a")

    def test_distinguishes_controlled_nonpassing_classes(self):
        self.assert_result("silence-timeout", b"")
        self.assert_result("malformed-protocol", b"not a terminal\n")
        self.assert_result("wrong-rejection", b"LEANOS/1 BOOTALLOC status=FAIL reason=other\n")
        self.assert_result("unexpected-success", b"LEANOS/1 CPL3 status=READY\n" + self.terminal.encode())
        self.assert_result(
            "unexpected-success",
            f"{PROTOCOL_PREFIX}22 ENTER origin=cpl3\n".encode()
            + self.terminal.encode(),
        )
        self.assert_result(
            "malformed-protocol",
            b"LEANOS/1 SERIAL status=READY\nLEANOS/1 UNKNOWN value=1\n"
            + self.terminal.encode(),
        )
        self.assert_result("malformed-protocol", self.terminal.encode())
        self.assert_result("post-terminal-output", self.terminal.encode() + b"\nextra\n")
        self.assert_result("malformed-protocol", self.terminal.encode() + b"\n" + self.terminal.encode())
        self.assert_result("malformed-protocol", b"\xff")

    def test_rejects_source_and_artifact_digest_drift(self):
        self.assert_result("digest-mismatch", self.terminal.encode(), revision="2" * 40)
        self.iso.write_bytes(b"changed")
        self.assert_result("digest-mismatch", self.terminal.encode())

    def test_rejects_incomplete_machine_identity(self):
        self.write_manifest(machine={})
        self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_invalid_expected_prefix(self):
        self.write_manifest(expectedPrefix=["unversioned output"])
        self.assert_result("manifest-invalid", self.terminal.encode())


if __name__ == "__main__":
    unittest.main()
