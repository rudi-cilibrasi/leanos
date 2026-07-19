#!/usr/bin/env python3
"""Controlled fixtures for the shared emulator evidence matrix."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
from unittest import mock


ROOT = Path(__file__).resolve().parent.parent
MODULE_PATH = ROOT / "scripts/run-emulator-evidence.py"
SPEC = importlib.util.spec_from_file_location("leanos_emulator_evidence", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load emulator evidence runner")
evidence = importlib.util.module_from_spec(SPEC)
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
    )
    return build, output, tools, args


def successful_runner(_command, *, env, **_kwargs):
    Path(env["LEANOS_SERIAL_LOG"]).write_text("typed fixture evidence\n", encoding="utf-8")
    return SimpleNamespace(returncode=0, stdout="QEMU command: fixture-qemu --checked\n")


def run_fixtures() -> None:
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)

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
            "mandatory fast-entry scenario is absent: return-fast-entry-sce-relaxation",
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
            "mandatory fast-entry scenario is absent: return-fast-entry-lstar-relaxation",
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
        with (
            mock.patch.object(evidence, "git_revision", return_value=revision),
            mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
            mock.patch.object(evidence.subprocess, "run", side_effect=successful_runner),
        ):
            evidence.run(args)

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
            _build, _output, _tools, case_args = prepare_tree(tmp / name)
            with (
                mock.patch.object(evidence, "git_revision", return_value=revision),
                mock.patch.object(evidence, "qemu_version", return_value="QEMU fixture"),
                mock.patch.object(evidence.subprocess, "run", side_effect=side_effect),
            ):
                expect_failure(lambda: evidence.run(case_args), fragment)

        evidence.check_workflows()

    print("Emulator evidence matrix fixtures passed")


if __name__ == "__main__":
    run_fixtures()
