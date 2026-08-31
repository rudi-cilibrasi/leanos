#!/usr/bin/env python3
"""Classify whether an explicit, no-fallback LeanOS KVM run is available."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import re
import stat
import subprocess
import sys
from typing import Callable


UNAVAILABLE = 20
ANSI_ESCAPE = re.compile(r"\x1b(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")


def first_cpu_model() -> str:
    try:
        for line in Path("/proc/cpuinfo").read_text(encoding="utf-8").splitlines():
            if line.startswith("model name") and ":" in line:
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return "unknown"


def base_result(device: Path, qemu: str, environment: dict[str, str]) -> dict[str, object]:
    return {
        "schema": "leanos-kvm-preflight-v1",
        "status": "unavailable",
        "reason": "probe-incomplete",
        "requested_accelerator": "kvm",
        "effective_accelerator": None,
        "fallback_allowed": False,
        "device": {
            "path": str(device),
            "exists": False,
            "character_device": False,
            "opened_read_write": False,
        },
        "qemu": {
            "binary": qemu,
            "version": "unknown",
            "accelerators": [],
            "guest_cpu": "max,vendor=AuthenticAMD",
            "runtime_marker": "unobserved",
        },
        "host": {
            "kernel": platform.platform(),
            "architecture": platform.machine(),
            "cpu_model": first_cpu_model(),
            "runner_os": environment.get("RUNNER_OS", "local"),
            "runner_arch": environment.get("RUNNER_ARCH", "local"),
            "runner_image_os": environment.get("ImageOS", "local"),
            "runner_image_version": environment.get("ImageVersion", "local"),
        },
        "source": {
            "revision": environment.get("GITHUB_SHA", "local"),
            "run_id": environment.get("GITHUB_RUN_ID", "local"),
            "run_attempt": environment.get("GITHUB_RUN_ATTEMPT", "local"),
        },
    }


def unavailable(result: dict[str, object], reason: str) -> tuple[int, dict[str, object]]:
    result["status"] = "unavailable"
    result["reason"] = reason
    result["effective_accelerator"] = None
    return UNAVAILABLE, result


def probe_kvm(
    device: Path,
    qemu: str,
    environment: dict[str, str],
    run: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
    open_device: Callable[..., int] = os.open,
    close_device: Callable[[int], None] = os.close,
) -> tuple[int, dict[str, object]]:
    result = base_result(device, qemu, environment)
    device_record = result["device"]
    qemu_record = result["qemu"]
    assert isinstance(device_record, dict)
    assert isinstance(qemu_record, dict)

    try:
        device_stat = device.stat()
    except FileNotFoundError:
        return unavailable(result, "device-missing")
    except PermissionError:
        return unavailable(result, "device-stat-permission-denied")
    except OSError as error:
        return unavailable(result, f"device-stat-error-{error.errno}")
    device_record["exists"] = True
    device_record["character_device"] = stat.S_ISCHR(device_stat.st_mode)
    if not device_record["character_device"]:
        return unavailable(result, "device-not-character")

    try:
        descriptor = open_device(device, os.O_RDWR | os.O_CLOEXEC)
    except PermissionError:
        return unavailable(result, "device-permission-denied")
    except OSError as error:
        return unavailable(result, f"device-open-error-{error.errno}")
    else:
        close_device(descriptor)
        device_record["opened_read_write"] = True

    try:
        version = run(
            [qemu, "--version"], env=environment, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=10, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return unavailable(result, "qemu-version-unavailable")
    version_lines = version.stdout.splitlines()
    if version.returncode != 0 or not version_lines:
        return unavailable(result, "qemu-version-unavailable")
    qemu_record["version"] = version_lines[0]

    try:
        accelerator_probe = run(
            [qemu, "-accel", "help"], env=environment, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=10, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return unavailable(result, "accelerator-list-unavailable")
    accelerators = [
        line.strip() for line in accelerator_probe.stdout.splitlines()
        if re.fullmatch(r"[a-z][a-z0-9_-]*", line.strip())
    ]
    qemu_record["accelerators"] = accelerators
    if accelerator_probe.returncode != 0:
        return unavailable(result, "accelerator-list-unavailable")
    if "kvm" not in accelerators:
        return unavailable(result, "accelerator-not-listed")

    command = [
        qemu,
        "-machine", "q35,accel=kvm",
        "-nodefaults",
        "-cpu", "max,vendor=AuthenticAMD",
        "-smp", "1",
        "-m", "128M",
        "-display", "none",
        "-serial", "none",
        "-monitor", "stdio",
    ]
    try:
        runtime = run(
            command, input="info kvm\nquit\n", env=environment, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=10, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return unavailable(result, "kvm-initialization-unavailable")
    normalized = ANSI_ESCAPE.sub("", runtime.stdout)
    marker_match = re.search(r"kvm support:\s*([a-z]+)", normalized)
    marker = marker_match.group(0) if marker_match else "unobserved"
    qemu_record["runtime_marker"] = marker
    if runtime.returncode != 0:
        return unavailable(result, "kvm-initialization-failed")
    if marker != "kvm support: enabled":
        return unavailable(result, "effective-accelerator-unconfirmed")

    result["status"] = "available"
    result["reason"] = "explicit-kvm-initialized"
    result["effective_accelerator"] = "kvm"
    return 0, result


def write_result(path: Path, result: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--device", type=Path, default=Path("/dev/kvm"))
    parser.add_argument("--qemu", default="qemu-system-x86_64")
    parser.add_argument(
        "--classify-unavailable",
        help="record a wrapper-level unavailability reason without probing",
    )
    args = parser.parse_args(argv)
    environment = os.environ.copy()
    if args.classify_unavailable:
        result = base_result(args.device, args.qemu, environment)
        status, result = unavailable(result, args.classify_unavailable)
    else:
        status, result = probe_kvm(args.device, args.qemu, environment)
    write_result(args.output, result)
    print(f"KVM preflight: {result['status']} ({result['reason']})")
    return status


if __name__ == "__main__":
    sys.exit(main())
