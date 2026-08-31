#!/usr/bin/env python3
"""Exercise QEMU's edu DMA engine against a protected guest-memory record.

This is deterministic QEMU integration evidence, not a hardware or refinement
proof.  The enabled control proves that the oracle observes a real device DMA
write.  The production-style control then clears PCI Command.bus-master, reads
it back, and proves the same requested transfer leaves the canary and its
fixture-owned allocator/frame identity metadata intact.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import select
import shutil
import subprocess
import sys
import tempfile
import time


EXPECTED_QEMU = (8, 2, 2)
EDU_BDF = (0, 2, 0)
EDU_IDENTITY = 0x11E81234
EDU_BAR = 0xFEA00000
SOURCE = 0x04000000
PROTECTED = 0x04001000
DEVICE_BUFFER = 0x40000
CANARY = bytes.fromhex("c35ac35ac35ac35a")
FRAME_IDENTITY = PROTECTED // 4096
ALLOCATOR_OWNER = 1
PROTECTED_RECORD = (
    CANARY
    + FRAME_IDENTITY.to_bytes(8, "little")
    + ALLOCATOR_OWNER.to_bytes(8, "little")
)
PAYLOAD = bytes.fromhex(
    "4c65616e4f532136"
    "ffffffffffffffff"
    "eeeeeeeeeeeeeeee"
)
PCI_COMMAND_MEMORY = 1 << 1
PCI_COMMAND_BUS_MASTER = 1 << 2
DMA_SOURCE = 0x80
DMA_DESTINATION = 0x88
DMA_COUNT = 0x90
DMA_COMMAND = 0x98
DMA_START = 1 << 0
DMA_FROM_DEVICE = 1 << 1
QTEST_RESPONSE_TIMEOUT_SECONDS = 5


def selected_accelerator() -> str:
    accelerator = os.environ.get("LEANOS_QEMU_ACCELERATOR", "tcg")
    if accelerator not in {"tcg", "kvm"}:
        raise RuntimeError(
            "QEMU accelerator must be exactly 'tcg' or 'kvm'; "
            "fallback lists are forbidden"
        )
    return accelerator


def selected_cpu() -> str:
    return (
        "max,vendor=AuthenticAMD"
        if selected_accelerator() == "kvm" else "max"
    )


class QTest:
    def __init__(self, executable: str) -> None:
        self.firmware = tempfile.NamedTemporaryFile(prefix="leanos-edu-", suffix=".bin")
        firmware = bytearray(b"\xff" * 65536)
        firmware[0xFFF0:0xFFF3] = b"\xf4\xeb\xfd"  # hlt; jmp back to hlt
        self.firmware.write(firmware)
        self.firmware.flush()
        self.process = subprocess.Popen(
            [
                executable,
                "-machine", f"q35,accel={selected_accelerator()}",
                "-nodefaults",
                "-cpu", selected_cpu(),
                "-smp", "1",
                "-m", "128M",
                "-display", "none",
                "-monitor", "none",
                "-serial", "none",
                "-bios", self.firmware.name,
                "-no-reboot",
                "-no-shutdown",
                "-nic", "none",
                "-device", "intel-iommu,intremap=off,pt=off,caching-mode=off,"
                           "device-iotlb=off,aw-bits=39,dma-translation=on,"
                           "snoop-control=off",
                "-device", "edu,bus=pcie.0,addr=0x2",
                "-qtest", "stdio",
            ],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

    def close(self) -> None:
        forced = False
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                forced = True
                self.process.kill()
                self.process.wait(timeout=2)
        if self.process.returncode not in (-15, 0) and not (
            forced and self.process.returncode == -9
        ):
            stderr = self.process.stderr.read() if self.process.stderr else ""
            raise RuntimeError(
                f"QEMU exited unexpectedly with {self.process.returncode}: "
                f"{stderr.strip()}"
            )
        self.firmware.close()

    def command(self, request: str) -> str:
        if self.process.stdin is None or self.process.stdout is None:
            raise RuntimeError("qtest pipes are unavailable")
        self.process.stdin.write(request + "\n")
        self.process.stdin.flush()
        readable, _, _ = select.select(
            [self.process.stdout],
            [],
            [],
            QTEST_RESPONSE_TIMEOUT_SECONDS,
        )
        if not readable:
            raise RuntimeError(
                f"qtest request {request!r} exceeded "
                f"{QTEST_RESPONSE_TIMEOUT_SECONDS}s response limit"
            )
        response = self.process.stdout.readline().strip()
        if not response.startswith("OK"):
            stderr = self.process.stderr.read() if self.process.poll() is not None else ""
            raise RuntimeError(f"qtest request {request!r} failed: {response} {stderr}")
        return response

    @staticmethod
    def config_address(offset: int) -> int:
        bus, device, function = EDU_BDF
        return (
            0x80000000
            | (bus << 16)
            | (device << 11)
            | (function << 8)
            | (offset & 0xFC)
        )

    def config_dword(self, offset: int) -> int:
        self.command(f"outl 0xcf8 0x{self.config_address(offset):08x}")
        response = self.command("inl 0xcfc").split()
        if len(response) != 2:
            raise RuntimeError(f"unexpected PCI read response: {response!r}")
        return int(response[1], 0)

    def set_config_dword(self, offset: int, value: int) -> None:
        self.command(f"outl 0xcf8 0x{self.config_address(offset):08x}")
        self.command(f"outl 0xcfc 0x{value:08x}")

    def write_bytes(self, address: int, value: bytes) -> None:
        for offset, byte in enumerate(value):
            self.command(f"writeb 0x{address + offset:x} 0x{byte:02x}")

    def read_aligned_qwords(self, address: int, count: int) -> bytes:
        if address % 8 != 0 or count % 8 != 0:
            raise RuntimeError("qword memory read must be 8-byte aligned")
        result = bytearray()
        for offset in range(0, count, 8):
            response = self.command(f"readq 0x{address + offset:x}").split()
            if len(response) != 2:
                raise RuntimeError(f"unexpected memory read response: {response!r}")
            result.extend(int(response[1], 0).to_bytes(8, "little"))
        return bytes(result)

    def writeq(self, offset: int, value: int) -> None:
        self.command(f"writeq 0x{EDU_BAR + offset:x} 0x{value:016x}")

    def readq(self, offset: int) -> int:
        response = self.command(f"readq 0x{EDU_BAR + offset:x}").split()
        if len(response) != 2:
            raise RuntimeError(f"unexpected MMIO read response: {response!r}")
        return int(response[1], 0)

    def transfer(
        self,
        source: int,
        destination: int,
        count: int,
        command: int,
    ) -> int:
        self.writeq(DMA_SOURCE, source)
        self.writeq(DMA_DESTINATION, destination)
        self.writeq(DMA_COUNT, count)
        self.writeq(DMA_COMMAND, command)
        deadline = time.monotonic() + QTEST_RESPONSE_TIMEOUT_SECONDS
        while time.monotonic() < deadline:
            observed = self.readq(DMA_COMMAND)
            if observed & DMA_START == 0:
                return observed
            time.sleep(0.001)
        raise RuntimeError("edu DMA transfer did not complete")


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


def exercise_case(executable: str, bus_master_enabled: bool) -> bytes:
    qtest = QTest(executable)
    try:
        if qtest.config_dword(0x00) != EDU_IDENTITY:
            raise RuntimeError("edu identity or pinned BDF drifted")
        qtest.set_config_dword(0x10, EDU_BAR)
        if qtest.config_dword(0x10) != EDU_BAR:
            raise RuntimeError("edu BAR assignment did not read back exactly")

        enabled = PCI_COMMAND_MEMORY | PCI_COMMAND_BUS_MASTER
        qtest.set_config_dword(0x04, enabled)
        if qtest.config_dword(0x04) & 0xFFFF != enabled:
            raise RuntimeError("edu enabled Command word did not read back exactly")
        qtest.write_bytes(SOURCE, PAYLOAD)
        if qtest.read_aligned_qwords(SOURCE, len(PAYLOAD)) != PAYLOAD:
            raise RuntimeError("edu DMA source did not read back exactly")
        if qtest.transfer(SOURCE, DEVICE_BUFFER, len(PAYLOAD), DMA_START) & DMA_START:
            raise RuntimeError("edu source transfer retained its run bit")

        qtest.write_bytes(PROTECTED, PROTECTED_RECORD)
        final_command = (
            enabled if bus_master_enabled else PCI_COMMAND_MEMORY
        )
        qtest.set_config_dword(0x04, final_command)
        if qtest.config_dword(0x04) & 0xFFFF != final_command:
            raise RuntimeError("edu final Command word did not read back exactly")
        completed_command = qtest.transfer(
            DEVICE_BUFFER,
            PROTECTED,
            len(PAYLOAD),
            DMA_START | DMA_FROM_DEVICE,
        )
        if completed_command & DMA_START:
            raise RuntimeError("edu protected transfer retained its run bit")
        observed = qtest.read_aligned_qwords(PROTECTED, len(PROTECTED_RECORD))
    finally:
        qtest.close()
    return observed


def exercise(executable: str) -> str:
    version = qemu_version(executable)
    quarantined_observed = exercise_case(executable, False)
    if quarantined_observed != PROTECTED_RECORD:
        raise RuntimeError(
            "bus-master-disabled edu changed the protected canary or "
            "allocator/frame identity"
        )
    enabled_observed = exercise_case(executable, True)
    if enabled_observed != PAYLOAD:
        raise RuntimeError(
            "enabled edu control did not change the complete protected record: "
            f"observed={enabled_observed.hex()} expected={PAYLOAD.hex()}"
        )

    return (
        "# leanos-q35-edu-dma-v2\n"
        f"# {version}\n"
        "bdf\tcommand\ttransfer\tprotected-frame\t"
        "canary-before\tcanary-after\tframe-identity-before\t"
        "frame-identity-after\tallocator-owner-before\t"
        "allocator-owner-after\tresult\n"
        f"00:02.0\t0002\tedu-to-guest\t{FRAME_IDENTITY}\t"
        f"{CANARY.hex()}\t{quarantined_observed[:8].hex()}\t"
        f"{FRAME_IDENTITY}\t"
        f"{int.from_bytes(quarantined_observed[8:16], 'little')}\t"
        f"{ALLOCATOR_OWNER}\t"
        f"{int.from_bytes(quarantined_observed[16:24], 'little')}"
        "\tQUARANTINED\n"
        f"00:02.0\t0006\tedu-to-guest\t{FRAME_IDENTITY}\t"
        f"{CANARY.hex()}\t{enabled_observed[:8].hex()}\t"
        f"{FRAME_IDENTITY}\t"
        f"{int.from_bytes(enabled_observed[8:16], 'little')}\t"
        f"{ALLOCATOR_OWNER}\t"
        f"{int.from_bytes(enabled_observed[16:24], 'little')}"
        "\tDMA-WRITE-OBSERVED\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--qemu", default="qemu-system-x86_64")
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    executable = shutil.which(args.qemu)
    if executable is None:
        parser.error(f"QEMU executable not found: {args.qemu}")
    try:
        report = exercise(executable)
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
