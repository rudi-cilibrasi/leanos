#!/usr/bin/env python3
"""Controlled fixtures for the bare-metal rejection classifier."""

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

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
        self.protocol = self.root / "serial-protocol.tsv"
        self.iso.write_bytes(b"iso")
        self.elf.write_bytes(b"elf")
        self.revision = "1" * 40
        self.protocol.write_text(
            "leanos-serial-protocol\t1\n"
            f"source-revision\t{self.revision}\n"
            f"record\t1\tSERIAL\tLEANOS_SERIAL_1_SERIAL\t{PROTOCOL_PREFIX}1 SERIAL\n"
            f"record\t3\tFINAL\tLEANOS_SERIAL_3_FINAL\t{PROTOCOL_PREFIX}3 FINAL\n"
            f"record\t3\tORACLE\tLEANOS_SERIAL_3_ORACLE\t{PROTOCOL_PREFIX}3 ORACLE\n"
            f"record\t7\tBOOTALLOC\tLEANOS_SERIAL_7_BOOTALLOC\t{PROTOCOL_PREFIX}7 BOOTALLOC\n"
            f"record\t8\tTERMINAL\tLEANOS_SERIAL_8_TERMINAL\t{PROTOCOL_PREFIX}8 TERMINAL\n"
            f"record\t22\tENTER\tLEANOS_SERIAL_22_ENTER\t{PROTOCOL_PREFIX}22 ENTER\n"
            f"record\t22\tBOOT\tLEANOS_SERIAL_22_BOOT\t{PROTOCOL_PREFIX}22 BOOT\n"
            f"record\t22\tOFFER\tLEANOS_SERIAL_22_OFFER\t{PROTOCOL_PREFIX}22 OFFER\n"
            f"record\t10\tIPC\tLEANOS_SERIAL_10_IPC\t{PROTOCOL_PREFIX}10 IPC\n"
            f"record\t15\tDMA\tLEANOS_SERIAL_15_DMA\t{PROTOCOL_PREFIX}15 DMA\n",
            encoding="utf-8",
        )
        with self.protocol.open("a", encoding="utf-8") as protocol:
            protocol.write(
                "pre-admission-boot-record\t22\tBOOT\n"
                "pre-admission-record\t15\tDMA\n"
                "pre-admission-reason\tdma-required-missing\n"
                "pre-admission-reason\tdma-inventory\n"
                "pre-admission-bootalloc-reason\tauthority-init\n"
            )
        self.serial = f"{PROTOCOL_PREFIX}1 SERIAL status=READY"
        self.boot = f"{PROTOCOL_PREFIX}22 BOOT scenario=capability-transfer"
        self.dma = f"{PROTOCOL_PREFIX}15 DMA snapshot=1 stage=pre-cpl3 result=PASS"
        self.terminal = f"{PROTOCOL_PREFIX}7 BOOTALLOC status=FAIL reason=authority-init"
        self.write_manifest()

    def tearDown(self):
        self.temp.cleanup()

    def write_manifest(self, **overrides):
        value = {
            "schemaVersion": 1,
            "sourceRevision": self.revision,
            "isoSha256": hashlib.sha256(self.iso.read_bytes()).hexdigest(),
            "elfSha256": hashlib.sha256(self.elf.read_bytes()).hexdigest(),
            "serialProtocolSha256": hashlib.sha256(
                self.protocol.read_bytes()
            ).hexdigest(),
            "expectedPrefix": [self.serial, self.boot, self.dma],
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
                               kwargs.get("revision", self.revision), self.protocol)

    def assert_result(self, result, text, **kwargs):
        with self.assertRaises(MODULE.ClassificationError) as caught:
            self.classify(text, **kwargs)
        self.assertEqual(caught.exception.result, result)

    def test_accepts_exact_final_rejection_and_binds_evidence(self):
        capture = (
            f"{self.serial}\r\n{self.boot}\r\n{self.dma}\r\n"
            + self.terminal
            + "\r\n"
        ).encode()
        normalized = capture.replace(b"\r\n", b"\n")
        result = self.classify(capture)
        self.assertEqual(result["result"], "exact-typed-rejection")
        self.assertEqual(result["captureBytes"], self.capture.stat().st_size)
        self.assertEqual(result["normalizedCaptureBytes"], len(normalized))
        self.assertEqual(
            result["normalizedCaptureSha256"],
            hashlib.sha256(normalized).hexdigest(),
        )
        self.assertEqual(result["captureLines"], 4)
        self.assertEqual(result["machine"]["model"], "fixture-board-rev-a")

    def test_emits_and_verifies_deterministic_bundle(self):
        capture = (f"{self.serial}\r\n{self.boot}\r\n{self.dma}\r\n"
                   + self.terminal + "\r\n").encode()
        result = self.classify(capture)
        bundle = self.root / "bundle"
        MODULE.emit_evidence_bundle(
            bundle, result, self.manifest, self.iso, self.elf, self.capture,
            self.protocol,
        )
        self.assertEqual(MODULE.verify_evidence_bundle(bundle), result)
        names = set(MODULE.BUNDLE_FILES) | {"SHA256SUMS"}
        self.assertEqual({path.name for path in bundle.iterdir()}, names)
        self.assertEqual(
            (bundle / "serial.normalized.log").read_bytes(),
            capture.replace(b"\r\n", b"\n"),
        )
        expected = [
            f"{MODULE.sha256(bundle / name)}  {name}" for name in MODULE.BUNDLE_FILES
        ]
        self.assertEqual((bundle / "SHA256SUMS").read_text().splitlines(), expected)

        (bundle / "serial.normalized.log").write_text("tampered\n")
        with self.assertRaises(MODULE.ClassificationError) as caught:
            MODULE.verify_evidence_bundle(bundle)
        self.assertEqual(caught.exception.result, "digest-mismatch")

    def test_accepts_only_generated_pre_admission_phase_prefixes(self):
        boot = f"{PROTOCOL_PREFIX}22 BOOT scenario=capability-transfer"
        dma = f"{PROTOCOL_PREFIX}15 DMA snapshot=1 stage=pre-cpl3 result=PASS"
        self.write_manifest(expectedPrefix=[
            f"{PROTOCOL_PREFIX}1 SERIAL status=READY",
            boot,
            dma,
        ])
        self.assertEqual(
            self.classify(
                (f"{PROTOCOL_PREFIX}1 SERIAL status=READY\n{boot}\n{dma}\n"
                 + self.terminal + "\n").encode()
            )["result"],
            "exact-typed-rejection",
        )

        ipc = f"{PROTOCOL_PREFIX}10 IPC event=boot"
        self.write_manifest(expectedPrefix=[ipc])
        self.assert_result("manifest-invalid", (ipc + "\n" + self.terminal).encode())

    def test_rejects_reordered_or_duplicate_pre_admission_phases(self):
        serial = f"{PROTOCOL_PREFIX}1 SERIAL status=READY"
        boot = f"{PROTOCOL_PREFIX}22 BOOT scenario=capability-transfer"
        dma = f"{PROTOCOL_PREFIX}15 DMA snapshot=1 result=PASS"

        for prefix in ([boot, serial, dma], [serial, boot, boot, dma], [serial, dma, boot]):
            with self.subTest(prefix=prefix):
                self.write_manifest(expectedPrefix=prefix)
                self.assert_result(
                    "manifest-invalid",
                    ("\n".join(prefix) + "\n" + self.terminal + "\n").encode(),
                )

    def test_requires_serial_and_boot_boundaries(self):
        for prefix in ([], [self.serial]):
            with self.subTest(prefix=prefix):
                self.write_manifest(expectedPrefix=prefix)
                self.assert_result(
                    "manifest-invalid",
                    ("\n".join(prefix + [self.terminal]) + "\n").encode(),
                )

    def test_requires_terminal_specific_phase_completeness(self):
        self.write_manifest(expectedPrefix=[self.serial, self.boot])
        self.assert_result(
            "manifest-invalid",
            (f"{self.serial}\n{self.boot}\n{self.terminal}\n").encode(),
        )

        final = f"{PROTOCOL_PREFIX}3 FINAL status=FAIL reason=dma-required-missing"
        self.write_manifest(expectedTerminal=final)
        self.assert_result(
            "manifest-invalid",
            (f"{self.serial}\n{self.boot}\n{self.dma}\n{final}\n").encode(),
        )

    def test_allows_repeated_records_within_a_generated_phase(self):
        serial = f"{PROTOCOL_PREFIX}1 SERIAL status=READY"
        boot = f"{PROTOCOL_PREFIX}22 BOOT scenario=capability-transfer"
        dma_one = f"{PROTOCOL_PREFIX}15 DMA snapshot=1 result=PASS"
        dma_two = f"{PROTOCOL_PREFIX}15 DMA snapshot=2 result=PASS"
        prefix = [serial, boot, dma_one, dma_two]
        self.write_manifest(expectedPrefix=prefix)

        result = self.classify(
            ("\n".join(prefix) + "\n" + self.terminal + "\n").encode()
        )

        self.assertEqual(result["result"], "exact-typed-rejection")

    def test_normalization_preserves_eof_and_replaces_lone_cr(self):
        without_final_newline = (
            f"{self.serial}\r{self.boot}\r{self.dma}\r" + self.terminal
        ).encode()
        normalized = without_final_newline.replace(b"\r", b"\n")

        result = self.classify(without_final_newline)

        self.assertEqual(result["result"], "exact-typed-rejection")
        self.assertEqual(result["normalizedCaptureBytes"], len(normalized))
        self.assertEqual(
            result["normalizedCaptureSha256"],
            hashlib.sha256(normalized).hexdigest(),
        )
        self.assertEqual(result["captureLines"], 4)

    def test_accepts_production_final_failure_as_the_expected_terminal(self):
        final_identity = PROTOCOL_PREFIX + "3 FINAL"
        self.terminal = f"{final_identity} status=FAIL reason=dma-required-missing"
        self.write_manifest(expectedPrefix=[self.serial, self.boot])

        result = self.classify(
            (f"{self.serial}\n{self.boot}\n" + self.terminal + "\n").encode()
        )

        self.assertEqual(result["result"], "exact-typed-rejection")

    def test_classifies_a_different_production_final_reason_as_wrong_rejection(self):
        final_identity = PROTOCOL_PREFIX + "3 FINAL"
        self.terminal = f"{final_identity} status=FAIL reason=dma-required-missing"
        self.write_manifest(expectedPrefix=[self.serial, self.boot])

        self.assert_result(
            "wrong-rejection",
            (f"{self.serial}\n{self.boot}\n" +
             f"{final_identity} status=FAIL reason=other\n").encode(),
        )

    def test_rejects_relabelled_nonterminal_protocol_identity(self):
        self.write_manifest(
            expectedTerminal=f"{PROTOCOL_PREFIX}3 ORACLE status=FAIL reason=made-up"
        )

        self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_a_runtime_final_reason_as_a_pre_admission_contract(self):
        self.write_manifest(
            expectedTerminal=f"{PROTOCOL_PREFIX}3 FINAL status=FAIL reason=entry-nested"
        )

        self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_a_non_emitter_bootalloc_reason(self):
        self.write_manifest(
            expectedTerminal=(
                f"{PROTOCOL_PREFIX}7 BOOTALLOC status=FAIL reason=not-an-emitter"
            )
        )

        self.assert_result("manifest-invalid", self.terminal.encode())

    def test_distinguishes_controlled_nonpassing_classes(self):
        self.assert_result("silence-timeout", b"")
        self.assert_result("malformed-protocol", b"not a terminal\n")
        self.assert_result("wrong-rejection", f"{PROTOCOL_PREFIX}7 BOOTALLOC status=FAIL reason=other\n".encode())
        self.assert_result("unexpected-success", f"{PROTOCOL_PREFIX}1 CPL3 status=READY\n".encode() + self.terminal.encode())
        self.assert_result(
            "unexpected-success",
            f"{PROTOCOL_PREFIX}22 ENTER origin=cpl3\n".encode()
            + self.terminal.encode(),
        )
        self.write_manifest(expectedPrefix=[
            f"{PROTOCOL_PREFIX}1 SERIAL status=READY",
            f"{PROTOCOL_PREFIX}22 OFFER origin=cpl3 result=PASS",
        ])
        self.assert_result("manifest-invalid", self.terminal.encode())
        self.write_manifest(expectedPrefix=[
            f"{PROTOCOL_PREFIX}1 SERIAL status=READY",
            f"{PROTOCOL_PREFIX}10 IPC event=enter subject=2 address-space=2 cpl=3 endpoint=10",
        ])
        self.assert_result("manifest-invalid", self.terminal.encode())
        self.write_manifest(expectedPrefix=[
            f"{PROTOCOL_PREFIX}1 SERIAL status=READY",
            f"{PROTOCOL_PREFIX}8 TERMINAL status=FAIL",
        ])
        self.assert_result("manifest-invalid", self.terminal.encode())
        self.write_manifest()
        self.assert_result(
            "malformed-protocol",
            f"{PROTOCOL_PREFIX}1 SERIAL status=READY\n{PROTOCOL_PREFIX}1 UNKNOWN value=1\n".encode()
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

    def test_rejects_non_string_revision_and_digest_fields(self):
        for field in (
            "sourceRevision",
            "isoSha256",
            "elfSha256",
            "serialProtocolSha256",
        ):
            with self.subTest(field=field):
                self.write_manifest(**{field: 1})
                self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_non_integer_schema_versions(self):
        for value in (True, "1"):
            with self.subTest(value=value):
                self.write_manifest(schemaVersion=value)
                self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_protocol_revision_and_row_contract_drift(self):
        self.protocol.write_text(
            self.protocol.read_text(encoding="utf-8").replace(
                self.revision, "2" * 40
            ),
            encoding="utf-8",
        )
        self.write_manifest()
        self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_incomplete_machine_identity(self):
        self.write_manifest(machine={})
        self.assert_result("manifest-invalid", self.terminal.encode())

        self.manifest.write_text("[]", encoding="utf-8")
        self.assert_result("manifest-invalid", self.terminal.encode())

        oversized = "x" * (MODULE.MAX_MACHINE_FIELD_CHARS + 1)
        self.write_manifest(machine={
            "model": oversized, "cpu": "fixture-x86-64",
            "firmware": "fixture-bios-1", "uart": "COM1 115200 8N1",
            "captureAdapter": "fixture-usb-uart",
        })
        self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_over_bound_files_before_classification(self):
        with patch.object(MODULE, "MAX_CAPTURE_BYTES", 2):
            self.assert_result("capture-failure", b"abc")
        with patch.object(MODULE, "MAX_MANIFEST_BYTES", 2):
            self.assert_result("manifest-invalid", self.terminal.encode())

    def test_rejects_invalid_expected_prefix(self):
        self.write_manifest(expectedPrefix=["unversioned output"])
        self.assert_result("manifest-invalid", self.terminal.encode())


if __name__ == "__main__":
    unittest.main()
