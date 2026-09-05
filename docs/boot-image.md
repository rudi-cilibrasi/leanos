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
of each boot scenario is its template in `scripts/expectations/`, rendered by
`scripts/run-image.sh` through the generated serial vocabulary; reordered,
missing, or extra records fail comparison. Version 1 below documents the
preceding Phase 1 protocol.

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

The versioned registry in `scripts/toolchain-profiles.json` separates the
canonical byte-reproducible reference from supported semantic-compatibility
profiles. The default `gcc-reference` environment is Ubuntu 24.04 (x86-64)
with the Lean version read from `lean-toolchain`. The canonical Ubuntu package
pins below are generated by `scripts/render-toolchain-consumers.py` from the
manifest; edit the manifest and regenerate rather than editing this table.

<!-- BEGIN GENERATED CANONICAL APT PACKAGES -->
| Package | Version |
| --- | --- |
| `binutils` | `2.42-4ubuntu2.10` |
| `ca-certificates` | `20260601~24.04.1` |
| `clang-18` | `1:18.1.3-1ubuntu1` |
| `coreutils` | `9.4-3ubuntu6.3` |
| `elan` | `3.1.0-1ubuntu0.1` |
| `gcc` | `4:13.2.0-7ubuntu1` |
| `gcc-13` | `13.3.0-6ubuntu2~24.04.1` |
| `git` | `1:2.43.0-1ubuntu7.3` |
| `grub-common` | `2.12-1ubuntu7.3` |
| `grub-pc-bin` | `2.12-1ubuntu7.3` |
| `libasan8` | `14.2.0-4ubuntu2~24.04.1` |
| `libubsan1` | `14.2.0-4ubuntu2~24.04.1` |
| `jq` | `1.7.1-3ubuntu0.24.04.2` |
| `make` | `4.3-4.1build2` |
| `mtools` | `4.0.43-1build1` |
| `python3` | `3.12.3-0ubuntu2.1` |
| `qemu-system-x86` | `1:8.2.2+ds-0ubuntu1.18` |
| `xorriso` | `1:1.5.6-1.1ubuntu3` |
<!-- END GENERATED CANONICAL APT PACKAGES -->

The scripts name the package pins in actionable missing-tool diagnostics.
The existing `clang-reference` profile changes only the C front end and its
reviewed final-ELF layout policy; it retains exact pins for every input.
Selection is explicit and compiler identity is checked before building:

```sh
LEANOS_TOOLCHAIN_PROFILE=gcc-reference ./scripts/build-image.sh
LEANOS_TOOLCHAIN_PROFILE=clang-reference LEANOS_CC=clang-18 \
  ./scripts/build-image.sh
```

Every image contains the resolved `TOOLCHAIN_PROFILE.json`, including the
registry hash and observed compiler identity. The same record is retained in
emulator evidence, reproducibility manifests, and release assets. See
[ADR 0014](adr/0014-toolchain-compatibility-profiles.md) for the distinction
between canonical reproducibility and supported semantic compatibility.

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
publishes the same centralized 41-artifact SHA-256 inventory from each, and
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

## Image-build phase timing evidence

Set `LEANOS_BUILD_TIMING_FILE` to retain a machine-readable timing record for an
image build:

```sh
LEANOS_BUILD_TIMING_FILE=build/ci/image-build-phases.tsv \
  ./scripts/build-image.sh
```

The TSV records six ordered, nonnegative phases and both the phase and
cumulative duration in whole seconds. `scripts/check-build-timing.py` rejects a
missing, reordered, malformed, or arithmetically inconsistent record before a
timed build can succeed. Controlled fixtures exercise those failures.

Required CI image producers set this path explicitly. Emulator shards bind the
record into their evidence tarballs; the primary and independent Clang builds,
release reproducibility builds, release gate, browser build, and optional
serial/graph comparison retain their records as 14-day workflow artifacts.
This first instrumentation slice for issue #266 makes duplicate work and slow
phases measurable before changing job or cache boundaries.

Durations are execution context, not deterministic build inputs. They are not
part of `REPRODUCIBILITY-SHA256SUMS`, and matching durations are not required
for byte reproducibility. Hosted scheduling, cache state, and runner load can
change them even when every admitted artifact remains identical.

The primary Clang lane builds and boots the canonical guest scenario with the pinned
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
GCC reference offsets. The selected profile applies no normalization for GCC
and recognizes only the enumerated Clang 18 offsets for the Clang profile. An
unknown profile or offset, extra site, changed instruction, different owner, or
new caller still fails closed.

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

`scripts/scenario-manifest.json` is the matrix's declarative sidecar. For each
scenario it records only what the row cannot express: the family whose
template the row must follow (fast-entry denial images, fast-entry return-path
relaxations, page-table-integrity probes), the family parameters (a corruption
mode, a rejection reason), which artifact kinds the scenario contributes to a
release and to the byte-reproducibility set, and its controlled-negative
evidence (directory, count, failure-class rule, driver). The evidence runner
derives everything else: `parse_matrix` checks each mandatory row against the
family template instead of a second hand-written copy and rejects a matrix
scenario without a manifest entry, `run-emulator-evidence.py
release-artifacts` and `reproducibility-artifacts` print the artifact lists
that `scripts/package-release.sh` and `scripts/write-reproducibility-manifest.sh`
iterate (neither names a `build/boot` artifact by hand), and
`scripts/verify-negative-evidence.sh` checks a scenario's recorded negatives
against the declared count and class, so the workflow no longer hard-codes
those numbers. A missing manifest entry, an unknown artifact kind, a family
parameter that disagrees with the matrix, a declared driver that does not
exist, or a derived artifact absent from the build each fail with a named
diagnostic; `scripts/test-emulator-evidence.py` exercises every one. The
manifest's `build` section declares the image wiring the same way: each kernel
object with its macro set, each boot object with its source and macro set,
each image as the boot and kernel objects it links (plus extra objects and
whether it receives a final page-plan link), and the policy-negative fixtures.
`scripts/generate-image-object-graph.py` derives its compile and link rules
from that section instead of Python literal tables, and it rejects an image
that names an unknown object or a malformed macro set with a named
diagnostic. The same section's `packaged_images` map declares, per final
ELF, the ISO it is staged into, the GRUB configuration that boots it, and the
final-ELF policy check queued for it (with an optional environment pair), and
`page_plan_stub_extras` names the page-plan headers the hand-linked images
need beyond those the kernel objects declare. `scripts/scenario-manifest.py`
prints those views as tab-separated rows, and `scripts/build-image.sh` loops
over them for the ISO staging roots, the page-plan stubs, the policy queue,
the image staging, and the ISO queue instead of listing every image by hand;
`scripts/test-scenario-manifest.py` rejects an invalid ISO name, an unknown
GRUB configuration, a duplicate policy key, a malformed environment pair, an
unknown kernel object, and a malformed stub name with named diagnostics. Four
ordered lists in the same section drive the remaining per-image steps in the
order the build runs them: `plan_checks` (a validate compares an image's
linker-resolved page-table plan with its expected header; a converge feeds
the resolved plan back through the listed graph targets until it is stable),
`disassemblies`, `entry_policies` (the entry-policy check queued per final
ELF with its report and optional environment pair), and
`extended_state_policies`; the query tool rejects an unpackaged image, an
unknown check kind, a convergence without graph targets or with a non-graph
target, a duplicated final plan or output, a duplicated policy key, and a
malformed variant, so the bespoke hand-linked double-fault family and the
tier-dependent fault-probe validation are the only per-image steps the build
script still spells out. A packaged image may also name its `port_sites`
inventory, the reviewed final-ELF port-I/O site list the build checks it
against; images that share a code layout share one inventory
(`scripts/direct-port-sites-user-probe.tsv` serves the three direct-port
probes and the adversarial-entry image), the query tool rejects a missing or
malformed inventory name, and the manifest test rejects two inventories with
identical contents so a duplicate cannot reappear.

Each boot-runner scenario also names its `expectations`: the template
`scripts/expectations/<boot scenario>.transcript` that `scripts/run-image.sh`
renders into the exact expected serial transcript. A template line is one
record, written as `@<family>/<TAG>@` followed by the record body, so the
serial vocabulary is spelled once in the generated `serial-protocol.sh` and
never by hand in a template; `@var:<name>@` substitutes one of the few values
the runner learns from the built image or the log (the frame-budget physical
frames, the fault-containment page, leaf, and address, and the
stale-translation CR3, RIP, and RSP), and the four markers `@common:prefix@`,
`@common:oracle@`, `@common:pre-cpl3@`, and `@common:controls@` expand to the
segments every boot scenario shares, which `scripts/expectation-template.sh`
spells once. The query tool's `expectations` view rejects a template that is
missing, misnamed, malformed, shared, or attached to a scenario that is not a
boot-runner row, and it rejects a boot-runner row without a template;
`scripts/check-expectation-templates.sh` renders every listed template without
QEMU and rejects an unresolved placeholder, an unknown record or variable, a
template that does not open with its BOOT record, or one whose common
segments are missing, duplicated, or out of protocol order. The runner itself
fails closed with `failure_class=runner-template` when a scenario has no
template. Adding a boot scenario is therefore a matrix row, a manifest entry
with its template, and the kernel fixture; the runner gains no new branch.

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
  the frame-budget, bounded capability-transfer, and in-flight revocation
  canonical-token bridges,
  distinct boot/scenario frame
  selection, and retire-before-republication ordering,
  and the manual `lean_uint64_dec_eq` implementation;
- the generated `composite-tokens.h`, `boundary-abi.h`, and
  `serial-protocol.h` headers, rendered by `scripts/generate-oracle.sh` from
  `LeanOS.BoundaryVocabulary`, from the Lean `@[export]` attributes, and from
  `LeanOS.SerialProtocol`. They are the only declarations of the boundary
  tokens, exported prototypes, and `LEANOS/<version> <TAG>` record prefixes
  that `boot/kernel.c`, `boot/boot.S`, and the hosted harnesses compile
  against; `include/leanos/composite-dispatcher.h` carries prose only, and the
  runner scripts source the sibling `serial-protocol.sh` for the same record
  prefixes. Generation removes transcription of a word, an arity, or a record
  identity; the generator, the awk renderers, and the compiler remain trusted,
  as for `corpus.h`.
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

`scripts/build-image.sh` starts each boot variant with a fixed-size placeholder
plan, links the image, and derives a plan from the linker-resolved symbols.
`scripts/generate-boot-page-plan.sh` passes those addresses to the host-only
`leanos-boot-plan` executable, which constructs all 8,192 candidate leaves,
both CR3 roots, all ancestor frames, and the validated boot reservation as one
`BootPageTablePlan.Input`. It emits the canonical PTE arrays only when
`BootPageTablePlan.compile` accepts that input. Variants whose compiled plan can
move a page boundary are rebuilt to a bounded fixed point. Every selected,
graph-owned ELF that shares the changed plan header is relinked before
validation; copied and policy-linked evidence artifacts stay outside that Make
invocation. Each assigned-EDU negative converges its own plan rather than
assuming the canonical image's code extent also covers its fixture-only failure
path. The build fails if any accepted plan does not stabilize within the bound.

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
