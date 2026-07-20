#!/usr/bin/env python3
"""Observe and check the pinned q35 PCI construction-time inventory.

This is QEMU integration evidence, not a guest boot-time quarantine check.  It
uses qtest to perform PCI configuration mechanism #1 reads while the machine is
paused before firmware runs.  The later guest read-back remains deliberately
separate because it must use issue #129's reviewed boot-only port authority.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass


EXPECTED_QEMU = (8, 2, 2)
BUS_MASTER = 1 << 2


@dataclass(frozen=True, order=True)
class Function:
    bus: int
    device: int
    function: int
    vendor: int
    product: int
    class_code: int
    command: int
    multifunction: bool

    @property
    def bdf(self) -> str:
        return f"{self.bus:02x}:{self.device:02x}.{self.function:x}"


EXPECTED = {
    (0, 0, 0): (0x8086, 0x29C0, 0x060000, False),
    (0, 1, 0): (0x1234, 0x1111, 0x030000, False),
    (0, 31, 0): (0x8086, 0x2918, 0x060100, True),
    (0, 31, 2): (0x8086, 0x2922, 0x010601, True),
    (0, 31, 3): (0x8086, 0x2930, 0x0C0500, True),
}


class QTest:
    def __init__(self, executable: str) -> None:
        command = [
            executable,
            "-machine", "q35,accel=tcg",
            "-cpu", "max",
            "-smp", "1",
            "-m", "128M",
            "-display", "none",
            "-monitor", "none",
            "-serial", "none",
            "-no-reboot",
            "-no-shutdown",
            "-nic", "none",
            "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
            "-S",
            "-qtest", "stdio",
        ]
        self.process = subprocess.Popen(
            command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

    def close(self) -> None:
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=2)
        if self.process.returncode not in (-15, 0):
            stderr = self.process.stderr.read() if self.process.stderr else ""
            raise RuntimeError(
                f"QEMU exited unexpectedly with {self.process.returncode}: {stderr.strip()}"
            )

    def command(self, request: str) -> str:
        if self.process.stdin is None or self.process.stdout is None:
            raise RuntimeError("qtest pipes are unavailable")
        self.process.stdin.write(request + "\n")
        self.process.stdin.flush()
        response = self.process.stdout.readline().strip()
        if not response.startswith("OK"):
            stderr = self.process.stderr.read() if self.process.poll() is not None else ""
            raise RuntimeError(f"qtest request {request!r} failed: {response} {stderr}")
        return response

    def config_dword(self, bus: int, device: int, function: int, offset: int) -> int:
        address = (
            0x80000000
            | (bus << 16)
            | (device << 11)
            | (function << 8)
            | (offset & 0xFC)
        )
        self.command(f"outl 0xcf8 0x{address:08x}")
        response = self.command("inl 0xcfc")
        fields = response.split()
        if len(fields) != 2:
            raise RuntimeError(f"unexpected qtest read response: {response!r}")
        return int(fields[1], 0)


def qemu_version(executable: str) -> str:
    completed = subprocess.run(
        [executable, "--version"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    first = completed.stdout.splitlines()[0]
    match = re.search(r"version (\d+)\.(\d+)\.(\d+)", first)
    if match is None or tuple(map(int, match.groups())) != EXPECTED_QEMU:
        raise RuntimeError(f"expected QEMU 8.2.2, got {first!r}")
    return first


def observe(executable: str) -> list[Function]:
    qtest = QTest(executable)
    found: list[Function] = []
    try:
        # Scan every function on the manifest's finite bus rather than trusting
        # function zero's multifunction bit to hide no unexpected function.
        for device in range(32):
            for function in range(8):
                identity = qtest.config_dword(0, device, function, 0x00)
                vendor = identity & 0xFFFF
                if vendor == 0xFFFF:
                    continue
                product = identity >> 16
                command = qtest.config_dword(0, device, function, 0x04) & 0xFFFF
                revision_class = qtest.config_dword(0, device, function, 0x08)
                class_code = revision_class >> 8
                header = qtest.config_dword(0, device, function, 0x0C)
                multifunction = bool((header >> 16) & 0x80)
                found.append(
                    Function(0, device, function, vendor, product, class_code,
                             command, multifunction)
                )
    finally:
        qtest.close()
    return found


def validate(functions: list[Function]) -> None:
    observed = {(f.bus, f.device, f.function): f for f in functions}
    if set(observed) != set(EXPECTED):
        missing = sorted(set(EXPECTED) - set(observed))
        extra = sorted(set(observed) - set(EXPECTED))
        raise RuntimeError(f"q35 inventory mismatch: missing={missing}, extra={extra}")
    for bdf, expected in EXPECTED.items():
        function = observed[bdf]
        actual = (
            function.vendor,
            function.product,
            function.class_code,
            function.multifunction,
        )
        if actual != expected:
            raise RuntimeError(
                f"identity mismatch at {function.bdf}: expected={expected}, actual={actual}"
            )
        if function.command & BUS_MASTER:
            raise RuntimeError(
                f"bus mastering enabled at construction time for {function.bdf}: "
                f"command=0x{function.command:04x}"
            )


def render(version: str, functions: list[Function]) -> str:
    lines = [
        "# leanos-q35-pci-construction-v1",
        f"# {version}",
        "# bdf\tvendor\tdevice\tclass\tcommand\tmultifunction\tbus-master",
    ]
    for function in functions:
        lines.append(
            f"{function.bdf}\t{function.vendor:04x}\t{function.product:04x}\t"
            f"{function.class_code:06x}\t{function.command:04x}\t"
            f"{int(function.multifunction)}\t{int(bool(function.command & BUS_MASTER))}"
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--qemu", default="qemu-system-x86_64")
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    executable = shutil.which(args.qemu)
    if executable is None:
        parser.error(f"QEMU executable not found: {args.qemu}")
    try:
        version = qemu_version(executable)
        functions = observe(executable)
        validate(functions)
        report = render(version, functions)
    except (OSError, subprocess.SubprocessError, RuntimeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(report, encoding="ascii")
    sys.stdout.write(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
