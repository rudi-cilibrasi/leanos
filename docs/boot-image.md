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

CI also has an experimental, non-blocking KVM lane. It admits exactly
`LEANOS_QEMU_ACCELERATOR=kvm`, never an accelerator fallback list, and runs the
same PR-tier scenarios only after a machine-readable probe confirms that the
host device and QEMU process are using KVM. Unavailable KVM is preserved as a
classification rather than counted as a passing boot. The fixed guest CPU
remains `max`; host CPU and runner variation are recorded as evidence context,
not admitted as guest-platform variation. See
[ADR 0013](adr/0013-kvm-on-host-evidence.md) for the trust distinction and the
criteria for any future promotion to a required check.

The topology-rejection runner is the deliberate exception to the singleton
launch shape. `scripts/run-multivcpu-rejection.sh` requests exactly
`-smp 2,sockets=1,cores=2,threads=1`, records the complete ordered QMP
`query-cpus-fast` exchange, and normalizes it into a versioned processor
inventory. It accepts only the exact topology rejection debug exit and terminal
record, with no CPL3, scheduler, timer, user-return, or post-terminal output.
The host QMP inventory independently proves which virtual processors QEMU
created; it does not authorize the guest decision or prove real-hardware/AP
semantics. Tagged-release diagnostics retain the raw `.qmp.jsonl` transcript
and normalized `.qmp.tsv` inventory alongside the serial log.

Run `./scripts/test-run-image.sh` to exercise controlled success, missing and
partial protocol, guest-error, and hang/timeout fixtures without booting QEMU.
These fixtures test the host harness only and are not boot evidence.

## Pinned reference tools

The reference environment is Ubuntu 24.04 (x86-64) with Lean 4.32.0 from
`lean-toolchain`, GCC 13.3.0 (`gcc=4:13.2.0-7ubuntu1`), GNU binutils 2.42
(`binutils=2.42-4ubuntu2.10`), GRUB
(`grub-common=2.12-1ubuntu7.3`, `grub-pc-bin=2.12-1ubuntu7.3`), mtools
(`mtools=4.0.43-1build1`), xorriso (`xorriso=1:1.5.6-1.1ubuntu3`), QEMU 8.2.2
(`qemu-system-x86=1:8.2.2+ds-0ubuntu1.18`), coreutils
(`coreutils=9.4-3ubuntu6.2`), and QEMU's distributed SeaBIOS 1.16.3 firmware.
The scripts name the Ubuntu package pins in actionable missing-tool diagnostics.

The independent Clang lane retains `-mgeneral-regs-only` and requests Lean's
required source-width floating-point evaluation contract. Clang 18 warns that
this evaluation method is unsupported on the resulting no-SSE target, so only
that `-Wpragmas` diagnostic remains non-fatal; the warning stays visible and all
source warnings remain errors. No floating-point operation is permitted by the
general-register-only target. The lane also uses `-fno-jump-tables`: the final
ELF entry-stack gate deliberately rejects indirect control-flow edges because
their possible targets cannot be bounded by its reviewed static call graph, and
Clang otherwise lowers the finite generated entry classifier through a jump
table. This preserves the fail-closed stack analysis rather than allowlisting
an optimizer-specific indirect edge.
These pins identify the build inputs. `build-image.sh` uses BIOS-only GRUB
output, a fixed ISO UUID and file dates, no linker build ID, and normalized
debug paths. Release CI and local validation retain
`./scripts/test-reproducible-build.sh` for same-runner checks. A pull request
promoted with the reviewed `ci:full-admission` label runs two Clang builds
concurrently on independent hosted runners,
publishes the same centralized 40-artifact SHA-256 inventory from each, and
compares those manifests in a fail-closed join job before `main` advances.
Ordinary pull requests retain bounded representative evidence for prompt
feedback. The strict default-branch ruleset requires the promoted full-evidence
join and requires the branch to be current with `main`; an update or subsequent
push therefore invalidates the old result and reruns the labeled admission.
The cross-runner comparison checks for hostname, path, timing, and other
runner-local leakage while removing one serial image build from the Clang
critical path. It measures same-revision rebuilding in the pinned reference
environment; it does not claim that arbitrary host distributions or tool
versions produce identical bytes.

The reviewable ruleset definition lives in
`.github/main-ruleset-policy.json`; a scheduled workflow compares GitHub's live
ruleset with that file and reports policy drift. The workflow also retains the
complete `merge_group` path for a future move to an organization-owned
repository, where GitHub makes merge queues available. The audit is
intentionally separate from per-commit admission so a transient API outage
cannot make otherwise valid changes unmergeable.

The primary Clang lane builds and boots the canonical image with the pinned
Ubuntu 24.04 `clang-18=1:18.1.3-1ubuntu1` package. Both independent full-build
lanes set `LEANOS_CC=clang-18`; the primary lane verifies nested compiler
selection, runs the final-ELF policy gates, and requires the canonical guest's
complete generated-oracle protocol plus independent debug-exit status. GCC and
Clang outputs are not compared: each compiler's same-revision rebuild is
compared only with itself. The lane preserves the compiler command, reviewed
security flags, ELF, map, disassembly/stack evidence, serial transcript, and
QEMU command log. GNU binutils, GRUB, SeaBIOS, and QEMU remain shared with the
reference lane, so this is independent C-front-end integration evidence—not
verified compilation, a semantic-equivalence proof, or a second release
toolchain.

The final-ELF direct-port gate continues to pin every reviewed symbol, opcode,
operand, owner, source invocation, and call-graph edge. Its manifest uses the
GCC reference offsets; the checker additionally recognizes only the enumerated
Clang 18 offsets produced by the pinned lane. An unknown offset, extra site,
changed instruction, different owner, or new caller still fails closed.

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
versioned, reviewable inventory used by both pull-request and tag CI. Its
`tier` column selects one representative scenario for every runner class on
pull requests; merge-queue candidates, pushes to `main`, tags, and releases
still execute every row.
Each row
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
remain workflow artifacts for 14 days. Each emulator shard stages them into one
tarball with an internal manifest of required paths, sizes, and SHA-256 hashes;
the bundler retains a diagnostic manifest but fails the job if a required file
is missing or differs from the passing evidence report. Controlled-negative
images are not permanent release assets because their hashes and results are
bound by the public manifest. The full Git commit is also stored as
`/boot/SOURCE_REVISION` inside the ISO; no wall-clock build timestamp is
embedded. GitHub's ephemeral workflow token publishes the release, and
OIDC-backed GitHub artifact attestations provide provenance without a
long-lived secret.

For the early-IDT rows, retained workflow evidence includes both probe ISOs,
final ELFs, maps, disassembly, final page-table plans, the early-IDT and
early-probe policy reports, exact serial logs with the early readiness and
terminal records, and the shared evidence directory's QEMU command, version,
and normalized QMP-runner transcript for the injected NMI.

For the multi-vCPU rejection row, retained evidence includes the exact escaped
QEMU command, raw QMP transcript, normalized ordered processor inventory, exact
pre-CPL3 rejection serial log, source revision, and the ordinary image's
ELF/map/disassembly and policy reports. This is tested QEMU/guest
correspondence under the documented q35/TCG boundary, not a proof of firmware,
APIC, reset, compiler, or physical-hardware behavior.

For the fast-entry rows, retained workflow evidence includes both probe ISOs,
final ELFs and maps, final page-table plans, exact serial logs, decoded
three-record CPU/CPUID/MSR/control snapshots, and final-ELF policy reports that
inventory the eight `wrmsr` sites, nine `rdmsr` sites, and the sole deliberate
probe opcode. The shared evidence directory binds the QEMU command and hashes;
the hosted oracle results retain all 241 vectors, including the 28-vector
direct-port-I/O corpus, the 32-vector
entry-control corpus, 10-vector fault-dispatch corpus, 23-vector contained
user-fault-class corpus, 17-vector NMI
classifier corpus, and 18-vector boot-interrupt-phase corpus; and the
entry-policy
fixture log records controlled
source/ELF rejection diagnostics. A missing artifact is visible because the
repository-owned bundler rejects a missing or stale passing row before CI
uploads its single tarball. These files are reproducibility and inspection
metadata, not proof of CPUID/MSR or exception semantics.

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
  System V ABI handoff, including the bootstrap IDT publications: the reviewed
  eleven-instruction pre-`lidt` prologue, the static `boot_idt32`/`boot_idt64`
  gate images and their terminal stubs, the one-instruction long-mode IDTR
  handoff, and NMI non-delivery inside those two residual windows;
- `boot/kernel.c`, including the bounded Multiboot2 byte parser, physical-frame
  scrub, UART polling, port I/O, QEMU debug-exit behavior, serial formatting,
  the frame-budget canonical-token bridge, distinct boot/scenario frame
  selection, and retire-before-republication ordering,
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
