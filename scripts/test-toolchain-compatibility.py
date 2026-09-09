#!/usr/bin/env python3
"""Fail-closed compatibility evidence and scheduling regression fixtures."""

from __future__ import annotations

import copy
from contextlib import redirect_stderr, redirect_stdout
import io
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("compatibility", ROOT / "scripts/toolchain-compatibility.py")
assert SPEC is not None and SPEC.loader is not None
compat = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(compat)


class CompatibilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data, self.entries = compat.registry()
        self.revision = "a" * 40
        self.reports = [{
            "schema": compat.SCHEMA, "profile": profile,
            "registry_sha256": compat.profiles.sha256(compat.profiles.DEFAULT_MANIFEST),
            "source_revision": self.revision, "status": "PASS",
            "phases": list(compat.PHASES),
            "semantic": {key: "b" * 64 for key in compat.SEMANTIC_FILES},
            "scenarios": compat.expected_scenarios(),
        } for profile in self.entries.values()]

    def test_complete_matrix_and_different_binary_hashes(self) -> None:
        for index, report in enumerate(self.reports):
            report["binary_sha256"] = str(index) * 64
        compat.compare(self.reports, self.revision)
        self.assertEqual(set(self.entries), {r["profile"] for r in compat.matrix()["include"]})

    def test_reject_incomplete_duplicate_unknown_and_malformed(self) -> None:
        for reports in ([], self.reports[:1], self.reports + self.reports[:1],
                        [None], [{"profile": {"id": []}}]):
            with self.subTest(reports=reports), self.assertRaises(compat.profiles.ProfileError):
                compat.compare(reports, self.revision)
        mutations = {
            "status": "FAIL", "schema": "unknown", "source_revision": "c" * 40,
            "registry_sha256": "d" * 64, "phases": list(compat.PHASES[:-1]),
            "profile": {"id": "unknown"}, "semantic": None, "scenarios": [],
        }
        for key, value in mutations.items():
            reports = copy.deepcopy(self.reports)
            reports[0][key] = value
            with self.subTest(field=key), self.assertRaises(compat.profiles.ProfileError):
                compat.compare(reports, self.revision)

    def test_each_semantic_and_guest_mutation_fails(self) -> None:
        for key in compat.SEMANTIC_FILES:
            reports = copy.deepcopy(self.reports)
            reports[1]["semantic"][key] = "e" * 64
            with self.subTest(contract=key), self.assertRaises(compat.profiles.ProfileError):
                compat.compare(reports, self.revision)
        for key, value in (("id", "invented"), ("status", "FAIL"),
                           ("runner_exit_status", 1), ("result_class", "wrong")):
            reports = copy.deepcopy(self.reports)
            # Even matching bad evidence across *all* compilers must fail.
            for report in reports:
                report["scenarios"][0][key] = value
            with self.subTest(guest=key), self.assertRaises(compat.profiles.ProfileError):
                compat.compare(reports, self.revision)

    def test_retained_contracts_are_rehashed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report = copy.deepcopy(self.reports[0])
            for name in compat.SEMANTIC_FILES:
                path = directory / f"{name}.txt"
                path.write_text("validated contract\n")
                report["semantic"][name] = compat.profiles.sha256(path)
            path = directory / "report.json"
            compat.write_report(path, report)
            self.assertEqual(compat.read_report(path), report)
            (directory / "oracle.txt").write_text("altered\n")
            with self.assertRaisesRegex(compat.profiles.ProfileError, "altered retained"):
                compat.read_report(path)

    def test_each_phase_fails_fast_and_retains_diagnostics(self) -> None:
        for failed_phase in compat.PHASES:
            with self.subTest(phase=failed_phase), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                output = directory / "report.json"
                commands = iter(compat.PHASES[1:])

                def execute(*args: object, **kwargs: object) -> subprocess.CompletedProcess:
                    phase = next(commands)
                    return subprocess.CompletedProcess(args, 1 if phase == failed_phase else 0)

                with patch.object(compat, "ROOT", directory), \
                     patch.object(compat, "registry", return_value=(self.data, self.entries)), \
                     patch.object(compat, "checked_output", return_value=self.revision), \
                     patch.object(compat, "environment", side_effect=(
                         compat.profiles.ProfileError("environment drift")
                         if failed_phase == "environment" else None)), \
                     patch.object(compat.subprocess, "run", side_effect=execute) as runner, \
                     redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                    with self.assertRaises(compat.profiles.ProfileError):
                        compat.run(self.data["default_profile"], output)
                report = json.loads(output.read_text())
                index = compat.PHASES.index(failed_phase)
                self.assertEqual(report["status"], "FAIL")
                self.assertEqual(report["phases"], list(compat.PHASES[:index]))
                self.assertEqual(runner.call_count, index)
                self.assertIn("completed_at", report)
                self.assertIn("error", report)

    def test_success_enumerates_modules_and_propagates_profile(self) -> None:
        profile = self.entries["clang-reference"]
        guest = {"results": [{
            "id": row["id"], "expected_result_class": row["result_class"],
            "status": "PASS", "runner_exit_status": 0,
        } for row in compat.expected_scenarios()]}
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / "LeanOS").mkdir()
            (directory / "LeanOS/Unimported.lean").write_text("example : True := True.intro\n")
            output = directory / "report.json"
            with patch.object(compat, "ROOT", directory), \
                 patch.object(compat, "registry", return_value=(self.data, self.entries)), \
                 patch.object(compat, "checked_output", return_value=self.revision), \
                 patch.object(compat, "environment"), \
                 patch.object(compat, "semantic_contract", return_value=self.reports[0]["semantic"]), \
                 patch.object(compat.profiles, "load_json", return_value=guest), \
                 patch.object(compat.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)) as runner, \
                 redirect_stdout(io.StringIO()):
                compat.run(profile["id"], output)
            report = json.loads(output.read_text())
            self.assertEqual(report["status"], "PASS")
            self.assertEqual(report["phases"], list(compat.PHASES))
            proof_command = runner.call_args_list[1].args[0]
            self.assertIn("LeanOS.Unimported", proof_command)
            for call in runner.call_args_list:
                env = call.kwargs["env"]
                self.assertEqual(env["LEANOS_CC"], "clang-18")
                self.assertEqual(env["LEANOS_HOST_CC"], "clang-18")
                self.assertEqual(env["LEANOS_ELF_LAYOUT_PROFILE"], "clang18-v1")

    def test_registry_rejects_unknown_tier_borrowed_layout_and_duplicate_keys(self) -> None:
        for key, value in (("evidence_tier", "latest"), ("apt_packages", ["binutils=1"]),
                           ("lean_toolchain", "leanprover/lean4:nightly")):
            data = copy.deepcopy(self.data)
            data["profiles"][1][key] = value
            with self.subTest(field=key), self.assertRaises(compat.profiles.ProfileError):
                compat.profiles.check_manifest(data)
        data = copy.deepcopy(self.data)
        data["profiles"][1]["interfaces"]["direct_port_elf"] = "gcc-reference-v1"
        with self.assertRaisesRegex(compat.profiles.ProfileError, "borrow"):
            compat.profiles.check_manifest(data)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "duplicate.json"
            path.write_text('{"status":"PASS","status":"FAIL"}')
            with self.assertRaisesRegex(compat.profiles.ProfileError, "duplicate JSON key"):
                compat.profiles.load_json(path)

    def test_candidate_inventory_can_change_without_changing_canonical(self) -> None:
        data = copy.deepcopy(self.data)
        candidate = copy.deepcopy(data["profiles"][1])
        candidate.update(id="clang-candidate", status="candidate")
        candidate["apt_packages"] = list(data["canonical_apt_packages"])
        old = candidate["shared_tools"]["xorriso"]
        new = "xorriso=1:1.5.6-1.1ubuntu4"
        candidate["apt_packages"][candidate["apt_packages"].index(old)] = new
        candidate["shared_tools"]["xorriso"] = new
        candidate["reference_environment"]["ci_image_digest"] = "sha256:" + "e" * 64
        data["profiles"].append(candidate)
        entries = compat.profiles.check_manifest(data)
        self.assertEqual(entries["gcc-reference"], self.entries["gcc-reference"])
        self.assertEqual(entries["clang-candidate"]["shared_tools"]["xorriso"], new)

    def test_environment_rejects_drift_before_building(self) -> None:
        profile = self.entries[self.data["default_profile"]]
        inventory = "\n".join(pin.replace("=", "\t", 1)
                              for pin in self.data["canonical_apt_packages"])
        outputs = ["x86_64", inventory, "Lean (version 4.32.0, release)"]
        with patch.dict(compat.os.environ, {
            "LEANOS_CI_IMAGE_DIGEST": profile["reference_environment"]["ci_image_digest"]
        }), patch.object(compat.profiles, "compiler_version", return_value="gcc (Ubuntu) 13.3.0"):
            with patch.object(compat, "checked_output", side_effect=outputs):
                compat.environment(profile, self.data)
            for index, replacement in ((0, "aarch64"), (1, "gcc\t0"),
                                       (2, "Lean (version 4.33.0, release)")):
                changed = list(outputs)
                changed[index] = replacement
                with self.subTest(component=index), \
                     patch.object(compat, "checked_output", side_effect=changed), \
                     self.assertRaises(compat.profiles.ProfileError):
                    compat.environment(profile, self.data)
        with patch.dict(compat.os.environ, {"LEANOS_CI_IMAGE_DIGEST": "sha256:" + "0" * 64}), \
             self.assertRaisesRegex(compat.profiles.ProfileError, "digest"):
            compat.environment(profile, self.data)

    def test_workflow_is_observational_and_retains_failures(self) -> None:
        from workflow_yaml import load_workflow

        workflow = load_workflow(ROOT / ".github/workflows/toolchain-compatibility.yml")
        self.assertEqual(workflow["permissions"], {"contents": "read"})
        self.assertEqual(workflow["on"]["schedule"], [{"cron": "23 4 * * *"}])
        self.assertIn("workflow_dispatch", workflow["on"])
        self.assertIn("scripts/**", workflow["on"]["pull_request"]["paths"])
        evidence = workflow["jobs"]["evidence"]
        self.assertEqual(evidence["container"], "${{ matrix.image }}")
        self.assertEqual(evidence["env"]["LEANOS_CI_IMAGE_DIGEST"], "${{ matrix.digest }}")
        self.assertFalse(evidence["strategy"]["fail-fast"])
        self.assertNotIn("continue-on-error", evidence)
        upload = evidence["steps"][-1]
        self.assertEqual(upload["if"], "always()")
        self.assertEqual(upload["with"]["if-no-files-found"], "error")
        comparison = workflow["jobs"]["compare"]
        self.assertIn("always()", comparison["if"])
        self.assertEqual(comparison["needs"], ["profiles", "evidence"])
        for job in workflow["jobs"].values():
            for step in job["steps"]:
                if "uses" in step:
                    self.assertRegex(step["uses"].split()[0], r"@[0-9a-f]{40}$")
                self.assertNotIn("continue-on-error", step)
        for path in (".github/workflows/ci.yml", "scripts/check.sh"):
            self.assertIn("python3 scripts/test-toolchain-compatibility.py", (ROOT / path).read_text())


if __name__ == "__main__":
    unittest.main()
