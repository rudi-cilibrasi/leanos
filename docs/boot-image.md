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

Version 14 adds two dedicated fast-entry-denial images. Subject A executes the
single allowlisted raw `SYSCALL` or `SYSENTER` opcode under the selected AMD
long-mode `-cpu max` contract. The exact transcript requires the kernel-owned
CPUID/MSR/control snapshot, vector-6 zero-error denial, an observation that no
alternate CPL0 target ran, complete cleanup of A, and restoration of B through
the sole validated `iretq` path with its CR3, stack, registers, and resources
intact.
The scenarios are separate mandatory rows in
`scripts/emulator-evidence-matrix.tsv`; neither observation establishes the
architectural behavior on another QEMU version or physical CPU.

Version 10 adds the scheduler-driven blocking-IPC slice in
[ADR 0009](adr/0009-blocking-ipc-boot.md). The exact trace starts B in CPL3,
records its empty receive and non-runnable state, dispatches A in A's address
space, records one accepted send and one ready insertion, restores B's saved
context and address space, and delivers the exact two-word payload with trusted
sender 1. Missing, reordered, duplicated, or forged records fail comparison.

Version 4 prefixes the version-3 subject trace with read-back evidence for
CR0.WP and CR4.SMEP and exact, one-shot CPL0 write-protection and SMEP page
faults. Their vector, error code, origin, and symbolic CR2 target are checked in
the guest before being emitted; no arbitrary kernel fault is recoverable.

Version 3 extends the boot evidence with the two-subject IPC boundary described
in [ADR 0004](adr/0004-two-subject-ipc-slice.md). It requires exact records for
both CPL3 subjects and address spaces, both directional denials, accepted send,
fixed handoff, delivered payload and kernel-derived provenance, non-transfer of
payload authority, contained fault, kernel resumption, and success. Version 2
extends the boot evidence with the ring-3 boundary described in
[ADR 0003](adr/0003-ring3-syscall-fault-slice.md). It requires, in order, a
CPL3 record, accepted and rejected syscall records, the expected vector-14
classification, kernel resumption, and final success. The complete exact trace
is encoded once in `scripts/run-image.sh`; reordered, missing, or extra records
fail comparison. Version 1 below documents the preceding Phase 1 protocol.

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

The reference environment is Ubuntu 24.04 (x86-64) with Lean 4.32.0 from
`lean-toolchain`, GCC 13.3.0 (`gcc=4:13.2.0-7ubuntu1`), GNU binutils 2.42
(`binutils=2.42-4ubuntu2.10`), GRUB
(`grub-common=2.12-1ubuntu7.3`, `grub-pc-bin=2.12-1ubuntu7.3`), mtools
(`mtools=4.0.43-1build1`), xorriso (`xorriso=1:1.5.6-1.1ubuntu3`), QEMU 8.2.2
(`qemu-system-x86=1:8.2.2+ds-0ubuntu1.17`), coreutils
(`coreutils=9.4-3ubuntu6.2`), and QEMU's distributed SeaBIOS 1.16.3 firmware.
The scripts name the Ubuntu package pins in actionable missing-tool diagnostics.
These pins identify the build inputs. `build-image.sh` uses BIOS-only GRUB
output, a fixed ISO UUID and file dates, no linker build ID, and normalized
debug paths. `./scripts/test-reproducible-build.sh` performs two clean builds
and requires byte-identical ISO, ELF, symbol map, and source-revision files.
The experiment is run by both release CI and local validation. It measures
same-revision rebuilding in the pinned reference environment; it does not claim
that arbitrary host distributions or tool versions produce identical bytes.

## Experimental releases

Tags and images use `vMAJOR.MINOR.PATCH` and `MAJOR.MINOR.PATCH`, respectively.
While LeanOS remains experimental, every GitHub release is a prerelease. A tag
is immutable release input: move neither a published tag nor its assets. Patch
increments are compatible experiment fixes, minor increments may change the
boot protocol or model, and major increments may change the target or research
scope. This policy is not a stability or support guarantee.

The tag workflow runs the repository-owned Markdown, complete Lean
proof-integrity, deterministic-build, image-build, and shared emulator-evidence
matrix before it can publish. `scripts/emulator-evidence-matrix.tsv` is the
versioned, reviewable inventory used by both pull-request and tag CI. Each row
names a unique scenario, its existing transcript-validating runner, expected
integration-evidence class, timeout, image and ELF, serial log, and fixture
metadata. New security-relevant QEMU work must register here; a reviewed matrix
version change is required to alter the mandatory release inventory.

`EMULATOR_EVIDENCE.json` binds every passing row to the full source revision,
matrix and tool-inventory hashes, QEMU version and exact command, runner result,
and hashes of the tested ISO, ELF, serial log, and command log. Packaging reruns
the verifier against the unchanged build tree and refuses missing, stale,
failed, reordered, or differently hashed evidence. The publishing job receives
only the already-gated bundle and alone has `contents`, OIDC, and attestation
write permissions.

Public assets include the default and preemption images, their debug files,
representative accepted/fail-stop serial logs, the matrix, compact evidence
manifest, source revision, deterministic toolchain manifest, experimental
notes, and SHA-256 manifest. All scenario images, serial logs, and command logs
remain workflow artifacts for 14 days; controlled-negative images are not
permanent release assets because their hashes and results are bound by the
public manifest. The full Git commit is also stored as `/boot/SOURCE_REVISION`
inside the ISO; no wall-clock build timestamp is embedded. GitHub's ephemeral
workflow token publishes the release, and OIDC-backed GitHub artifact
attestations provide provenance without a long-lived secret.

For the fast-entry rows, retained workflow evidence includes both probe ISOs,
final ELFs and maps, final page-table plans, exact serial logs, decoded
three-record CPU/CPUID/MSR/control snapshots, and final-ELF policy reports that
inventory the eight `wrmsr` sites, nine `rdmsr` sites, and the sole deliberate
probe opcode. The shared evidence directory binds the QEMU command and hashes;
the hosted oracle results retain all 182 vectors, including the 28-vector
direct-port-I/O corpus, the 32-vector
entry-control corpus and 10-vector fault-dispatch corpus; and the entry-policy
fixture log records controlled
source/ELF rejection diagnostics. A missing artifact is visible because the CI
upload uses named paths and the evidence packager rejects a missing or stale
passing row. These files are reproducibility and inspection metadata, not
proof of CPUID/MSR or exception semantics.

After downloading every release asset into one directory, verify it with:

```sh
sha256sum --check SHA256SUMS
gh attestation verify --repo rudi-cilibrasi/leanos \
  leanos-0.1.0-x86_64.iso
cat SOURCE_REVISION
```

Repeat `gh attestation verify` for the ELF, map, logs, evidence manifest and
matrix, revision, toolchain, notes, and checksum manifest. Compare
`SOURCE_REVISION` with the tag using
`git rev-list -n 1 v0.1.0`. The attestation establishes where GitHub Actions
built an artifact and the checksums detect changed bytes; neither proves the
binary implements the Lean model. Matrix result classes describe deterministic
integration behavior across trusted boundaries; none is a Lean proof or binary
refinement theorem. The release's `RELEASE_NOTES.md` explicitly
enumerates the experimental status, TCB, and unproved model-to-binary boundary.

## Trusted boundary

The following new code and assumptions are trusted, not proved:

- `boot/boot.S`, the Multiboot2 header, page tables, GDT, x86-64 mode switch,
  CR0.WP/CR4.SMEP writes and CPU-feature assumption, stack, fault probes, and
  System V ABI handoff;
- `boot/kernel.c`, including the bounded Multiboot2 byte parser, physical-frame
  scrub, UART polling, port I/O, QEMU debug-exit behavior, serial formatting,
  and the manual `lean_uint64_dec_eq` implementation;
- the fast-entry CPU/MSR bridge: CPUID vendor/feature decoding, privileged
  `rdmsr`/`wrmsr`, EFER reserved-bit handling, the assumed AMD long-mode
  `SYSCALL`/`SYSENTER` denial semantics and exception priority, vector-6 frame
  construction, cleanup/restore code, and the final pre-`iretq` readback;
- Lean code generation and generated C, GCC, GNU assembler/linker and linker
  garbage collection, the linker script, GRUB, SeaBIOS, QEMU, and the x86-64,
  Multiboot2, 16550 UART, and emulated-device contracts.

The build uses function/data sections and fails on every undefined symbol. This
keeps the boot-reachable Lean runtime shim inventory to scalar equality. Adding
another primitive, foreign declaration, assembly file, device, or runtime
service must update this inventory. The generated code and machine execution
are integration-tested; neither compilation nor QEMU success proves refinement
to the Lean model or verifies the boot chain.

## Linked page-table plan boundary

`scripts/build-image.sh` now performs a size-stable two-pass link for each boot
variant. The prelink uses fixed-size placeholder arrays solely to determine the
final linker symbol addresses. `scripts/generate-boot-page-plan.sh` passes those
addresses to the host-only `leanos-boot-plan` executable, which constructs all
8,192 candidate leaves, both CR3 roots, all ancestor frames, and the validated
boot reservation as one `BootPageTablePlan.Input`. It emits the canonical PTE
arrays only when `BootPageTablePlan.compile` accepts that input. The final link
is rejected if regenerating from its symbols changes the emitted arrays.

The early assembly still constructs paging before generated Lean code can run.
After paging is active, the guest walker decodes both complete live hierarchies
and compares every ancestor slot and leaf with the generated arrays. Subject A
and B pages are absent from the other subject's root, both selected CR3 values
are checked, and controlled mutations of live inactive tables must be rejected.
CI preserves the prelink map, accepted header, regenerated final header, final
map/ELF, and serial records so the boundary can be reproduced and inspected.

This is a proved property of accepted plan values plus tested correspondence at
the build and QEMU boundaries. Symbol extraction, the size-stability argument,
header transport, compiler/linker behavior, assembly stores, guest pointer
chasing, CR3 hardware semantics, and QEMU remain explicitly trusted. The
guard-mapped double-fault negative is a selected test-policy deviation: its one
guard leaf is expected live by the variant checker but is not part of the normal
accepted boot plan.
