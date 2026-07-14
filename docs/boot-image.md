# Phase 1 x86-64 boot image

Build the versioned ISO from a fresh clone with:

```sh
./scripts/build-image.sh
```

Boot it headlessly, validate the complete serial transcript, and require the
guest success signal with:

```sh
./scripts/run-image.sh
```

The build emits `build/boot/leanos-0.1.0-x86_64.iso`, its checksums, the
unstripped debug ELF `build/boot/leanos.elf`, and `build/boot/leanos.map`.
Generated files are ignored; every byte in the image is rebuilt from source or
from the documented toolchain. There are no repository-supplied binary blobs.

## Stable protocol and termination

Version 1 is exactly four newline-terminated ASCII records:

```text
LEANOS/1 BOOT target=x86_64-q35
LEANOS/1 TRANSITION state=0 command=1 result=1
LEANOS/1 TRANSITION state=0 command=7 result=0
LEANOS/1 FINAL status=PASS
```

The two transition records invoke the exact generated-C export
`leanos_boot_transition`, checking its accepted and rejected encodings. The
guest writes `0x10` to QEMU's `isa-debug-exit` device for success (`qemu` status
33) and `0x11` for failure (status 35). The host script also has a 30-second
timeout, rejects any missing/reordered/trailing serial data, disables networking,
and uses one `q35` CPU under TCG.

The runner fixes the machine (`q35`), CPU (`max`), memory (128 MiB), one vCPU,
ISO image, file-backed serial console, and software-only TCG acceleration, so it
does not require KVM. Allow roughly 256 MiB of host memory, 100 MiB of disk for
build artifacts, and at most 30 seconds of wall time. It always creates and
preserves `build/boot/serial.log`, and prints the QEMU version, exact escaped
command, and a `timeout`, `guest-error`, `qemu-error`, or `serial-protocol`
failure class. Success requires both debug-exit status 33 and the exact protocol.

Run `./scripts/test-run-image.sh` to exercise controlled success, missing and
partial protocol, guest-error, and hang/timeout fixtures without booting QEMU.
These fixtures test the host harness only and are not boot evidence.

## Pinned reference tools

The reference environment is Ubuntu 24.04 with Lean 4.32.0 from
`lean-toolchain`, GCC 13.3.0 (`gcc=4:13.2.0-7ubuntu1`), GNU binutils 2.42
(`binutils=2.42-4ubuntu2.10`), GRUB
(`grub-common=2.12-1ubuntu7.3`, `grub-pc-bin=2.12-1ubuntu7.3`), mtools
(`mtools=4.0.43-1build1`), xorriso (`xorriso=1:1.5.6-1.1ubuntu3`), QEMU 8.2.2
(`qemu-system-x86=1:8.2.2+ds-0ubuntu1.17`), coreutils
(`coreutils=9.4-3ubuntu6.2`), and QEMU's distributed SeaBIOS 1.16.3 firmware.
The scripts name the Ubuntu package pins in actionable missing-tool diagnostics.
These pins identify build inputs; this issue does not claim byte-for-byte
reproducibility.

## Trusted boundary

The following new code and assumptions are trusted, not proved:

- `boot/boot.S`, the Multiboot2 header, page tables, GDT, x86-64 mode switch,
  stack, and System V ABI handoff;
- `boot/kernel.c`, including UART polling, port I/O, QEMU debug-exit behavior,
  serial formatting, and the manual `lean_uint64_dec_eq` implementation;
- Lean code generation and generated C, GCC, GNU assembler/linker and linker
  garbage collection, the linker script, GRUB, SeaBIOS, QEMU, and the x86-64,
  Multiboot2, 16550 UART, and emulated-device contracts.

The build uses function/data sections and fails on every undefined symbol. This
keeps the boot-reachable Lean runtime shim inventory to scalar equality. Adding
another primitive, foreign declaration, assembly file, device, or runtime
service must update this inventory. The generated code and machine execution
are integration-tested; neither compilation nor QEMU success proves refinement
to the Lean model or verifies the boot chain.
