#!/usr/bin/env python3
"""Controlled positives and negatives for the KVM availability classifier."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import stat
import subprocess
from types import SimpleNamespace
from unittest import mock


ROOT = Path(__file__).resolve().parent.parent
MODULE_PATH = ROOT / "scripts/probe-kvm.py"
SPEC = importlib.util.spec_from_file_location("leanos_probe_kvm", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load KVM preflight")
probe = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(probe)


def completed(command: list[str], output: str, status: int = 0) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(command, status, output)


def scripted_run(mode: str):
    def run(command, **_kwargs):
        if command[1:] == ["--version"]:
            return completed(command, "QEMU emulator version fixture\n")
        if command[1:] == ["-accel", "help"]:
            accelerators = "tcg\n" if mode == "missing-kvm" else "tcg\nkvm\n"
            return completed(command, accelerators)
        if mode == "initialization-failure":
            return completed(command, "failed to initialize kvm\n", 1)
        marker = "disabled" if mode == "fallback" else "enabled"
        return completed(command, f"kvm support: {marker}\n")
    return run


def run_fixture(mode: str):
    character = SimpleNamespace(st_mode=stat.S_IFCHR)
    with (
        mock.patch.object(Path, "stat", return_value=character),
        mock.patch.object(Path, "exists", return_value=True),
    ):
        return probe.probe_kvm(
            Path("/fixture/kvm"), "qemu-fixture", {}, run=scripted_run(mode),
            open_device=lambda *_args: 7, close_device=lambda _descriptor: None,
        )


status, result = run_fixture("available")
assert status == 0
assert result["status"] == "available"
assert result["effective_accelerator"] == "kvm"
assert result["fallback_allowed"] is False
assert result["qemu"]["runtime_marker"] == "kvm support: enabled"
assert result["qemu"]["guest_cpu"] == "max,vendor=AuthenticAMD"

status, result = run_fixture("missing-kvm")
assert status == probe.UNAVAILABLE
assert result["reason"] == "accelerator-not-listed"

status, result = run_fixture("fallback")
assert status == probe.UNAVAILABLE
assert result["reason"] == "effective-accelerator-unconfirmed"
assert result["effective_accelerator"] is None

status, result = run_fixture("initialization-failure")
assert status == probe.UNAVAILABLE
assert result["reason"] == "kvm-initialization-failed"

character = SimpleNamespace(st_mode=stat.S_IFCHR)
with (
    mock.patch.object(Path, "stat", return_value=character),
    mock.patch.object(Path, "exists", return_value=True),
):
    def deny_open(*_args):
        raise PermissionError

    status, result = probe.probe_kvm(
        Path("/fixture/kvm"), "qemu-fixture", {}, open_device=deny_open
    )
assert status == probe.UNAVAILABLE
assert result["reason"] == "device-permission-denied"

with mock.patch.object(Path, "stat", side_effect=FileNotFoundError):
    status, result = probe.probe_kvm(Path("/fixture/missing"), "qemu-fixture", {})
assert status == probe.UNAVAILABLE
assert result["reason"] == "device-missing"

print("KVM preflight positive and controlled-negative checks passed")
