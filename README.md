# LeanOS

LeanOS is an experiment in building a small operating-system kernel whose
implementation, executable specification, and machine-checked proofs evolve
together in Lean 4.

The project is at the **concept and bootstrap stage**. There is no bootable
kernel yet, and none of the security properties below should be read as a
current guarantee. The immediate goal is deliberately smaller: boot a minimal
image under QEMU, exercise it deterministically in CI, and prove useful
properties about its first kernel abstractions.

## Why LeanOS?

Projects such as seL4 show the value of connecting a kernel implementation to a
formal model. LeanOS explores how much of that connection can live in one Lean
4 codebase:

- executable models beside the theorems that constrain them;
- small kernel interfaces with explicit preconditions and postconditions;
- proof-carrying changes checked on every pull request;
- emulator tests that connect abstract claims to a bootable artifact; and
- a documented trusted computing base (TCB), including every unverified bridge
  between Lean, generated code, the runtime, the linker, and hardware.

This is a research project, not a claim that writing code in Lean automatically
makes an operating system verified. Compiler correctness, runtime behavior,
foreign code, boot code, device models, and hardware assumptions all matter.
Making those boundaries visible is part of the work.

## Project principles

1. **State claims precisely.** Every advertised guarantee must name its model,
   assumptions, proof, and executable boundary.
2. **Keep the TCB small and visible.** Unverified assembly, C, firmware, tools,
   and runtime components are tracked rather than hidden behind “verified.”
3. **Prove vertical slices.** Prefer a tiny path from specification to booted
   behavior over a broad collection of disconnected theorems.
4. **Test the boundary.** Proofs cover models; QEMU and hardware tests cover the
   integration points where those models meet reality.
5. **Reproduce everything.** Pin toolchains and make local and CI commands use
   the same scripts.

## First vertical slice

The first credible milestone is a deterministic, headless QEMU boot that:

1. loads a versioned x86-64 image;
2. initializes the minimum required runtime;
3. prints a known message over the serial console;
4. exercises one Lean-specified kernel state transition;
5. exits QEMU with a machine-readable success code; and
6. is built, proved, booted, and checked by GitHub Actions.

The implementation language and ABI at the boot boundary are not decided yet.
An early toolchain spike will determine whether Lean-generated code can be used
freestanding with a suitably small runtime or whether the first slice needs a
minimal assembly/C/Rust loader around a Lean model. The decision and its TCB
impact will be recorded before the kernel architecture hardens.

The target platform, Phase 1 threat model, proof vocabulary, allowed milestone
claims, and initial trusted computing base are fixed in
[ADR 0001](docs/adr/0001-phase-1-scope-threat-model-and-tcb.md). In particular,
successful compilation or QEMU execution is integration evidence, not proof of
the generated binary or boot chain.

[ADR 0002](docs/adr/0002-freestanding-lean-boundary.md) selects a restricted,
allocation-free generated-C export for the first Lean/boot boundary and records
the reproducible experiments and trusted assumptions behind that decision.

The Phase 1 image can be built with `./scripts/build-image.sh` and exercised
headlessly with `./scripts/run-image.sh`; the stable protocol, pinned reference
tools, debug artifacts, and added trusted boundary are documented in
[the boot-image guide](docs/boot-image.md).

The first Phase 2 executable boundary boots one deliberately tiny ring-3
subject through an `int 0x80` gate, binds its calls to kernel-selected context,
and contains one expected user page fault. Its assumptions and evidence are
recorded in [ADR 0003](docs/adr/0003-ring3-syscall-fault-slice.md).

The two-subject integration slice extends that boundary with separate page
tables and a fixed cooperative handoff through one directional endpoint. Its
tested behavior and unproved machine boundary are recorded in
[ADR 0004](docs/adr/0004-two-subject-ipc-slice.md).

The first executable model is `LeanOS.KernelTransition.transition`, with
machine-checked determinism, invariant-preservation, and rejection-stability
theorems in
[`LeanOS/KernelTransition.lean`](LeanOS/KernelTransition.lean). The boot-slice
[issue #6](https://github.com/rudi-cilibrasi/leanos/issues/6) must invoke the
exact fixed-width export `LeanOS.KernelTransition.bootTransition` (C symbol
`leanos_boot_transition`) and test its encoded accepted and rejected results.
That adapter is proved to agree with the model for well-formed encoded states;
the generated code and boot boundary remain trusted rather than proved.

The first capability-security reference model is documented in
[`docs/capability-model.md`](docs/capability-model.md). Its Lean theorems prove
well-formedness preservation, state-preserving rejection, and authority
provenance for a minimal copy/revoke operation set. These are model-level
properties, not claims about information flow, covert channels, concurrency,
object lifetimes, generated code, or a kernel binary.

The physical-frame allocator reference model and its representation,
complexity, initialization assumptions, proved invariants, and capability
ownership boundary are documented in
[`docs/frame-allocator.md`](docs/frame-allocator.md).

The first composition of capability authority with frame ownership uses
never-reused object identifiers to prove safe release and reuse; its lifetime
rule, machine-checked guarantees, executable attacks, and limits are documented
in [`docs/memory-lifecycle.md`](docs/memory-lifecycle.md).

The executable virtual-mapping model adds subject-owned address spaces,
capability-bounded read/write mappings, live translation checks, and stale
mapping invalidation. Its policy, proved scope, examples, and limitations are
documented in [`docs/virtual-mapping.md`](docs/virtual-mapping.md).

The executable [x86-64 page-table refinement model](docs/x86-page-tables.md)
encodes that policy into a constrained 4 KiB, four-level paging subset and
proves structural validity, permission non-amplification, current-frame
agreement, NX enforcement, and cross-address-space separation. Hardware walks,
CR3/TLB operations, boot integration, and the compiler remain trusted.

The first total syscall model separates trusted caller/active-address-space
context from untrusted fixed-width scalar words and proves invariant
preservation, rejection stability, and caller confinement. Its vocabulary and
trust boundary are documented in [`docs/syscall-model.md`](docs/syscall-model.md).

The endpoint IPC model provides capability-authorized, capacity-one,
nonblocking mailboxes with trusted sender provenance, never-reused endpoint
identities, and complete destruction cleanup. Its precise proof boundary and
exclusions are documented in [`docs/endpoint-ipc.md`](docs/endpoint-ipc.md).

The bounded [user-copy model](docs/user-copy.md) prevalidates a small complete
range through current virtual mappings before changing typed kernel buffers or
live-frame byte memory, with explicit alias rejection and atomic failure.

The [frame-scrubbing model](docs/frame-scrubbing.md) atomically clears reused
frame contents before publishing a fresh memory-object lifetime and proves
modeled reads cannot expose an earlier owner's bytes before the new owner
writes.

The [subject-lifecycle model](docs/subject-lifecycle.md) gives subjects
never-reused identities and defines atomic termination cleanup across held
capabilities, exclusively owned memory, address spaces, endpoints, pending
provenance, and runnable/current state.

The bounded [model-oracle corpus](docs/model-oracle.md) is evaluated in Lean
and replayed through hosted generated code and every boot-reachable adapter.
This differential check detects integration mismatches; it is not compiler or
binary verification.

The [interrupt model](docs/interrupt-model.md) gives the initial page-fault,
timer, and syscall vector vocabulary, proves origin-sensitive dispatch and
whole-subject user-fault containment, and records the unproved x86 entry and
return boundary.

The [observer-relative isolation model](docs/observation-model.md) defines a
subject's authorized view and proves scoped one-step low-equivalence and equal
visible replies for unrelated sequential operations over disjoint actor-local
memory. Authorized IPC and aliased shared memory/capabilities, global resource
exhaustion, and visible scheduling are explicit
channels; this is not a binary-level or timing-sensitive confidentiality claim.

## Verification targets

These are directions, not completed features. Work should land incrementally
with an explicit threat model and proof statement.

- **Functional correctness:** kernel operations refine a small abstract state
  machine and satisfy documented API contracts.
- **Capability safety:** authority is explicit, unforgeable in the model, and
  cannot be amplified by kernel operations.
- **Isolation and information flow:** subjects cannot observe or modify state
  outside their authority, modulo documented channels and assumptions.
- **Memory safety:** allocation, mapping, and object lifetimes preserve
  separation and ownership invariants.
- **Crash and recovery behavior:** persistent operations have specified atomic
  outcomes under modeled interruption.
- **Liveness and resource bounds:** selected operations terminate and critical
  resources have enforceable limits.
- **Boot integrity:** measured artifacts correspond to reviewed sources and a
  documented build process.

## CI strategy

GitHub-hosted Linux runners can run QEMU without hardware acceleration. That is
slower than KVM but suitable for a small, deterministic boot-smoke test.

CI will grow in layers:

| Layer | Gate | Status |
| --- | --- | --- |
| Repository | Markdown and repository hygiene | Active |
| Lean | Build all modules and check proofs with a pinned toolchain | Active |
| Host tests | Run pure state-machine and property tests | Planned |
| Emulator | Build and boot headlessly with timeout and serial assertions | Active |
| Artifacts | Preserve image, ELF, map, checksums, versions, and serial log | Active |
| Release | Publish tagged reproducible images with provenance | Active |

Emulator CI should invoke one repository-owned script, use an explicit timeout,
capture the serial console, and require a guest success signal. A process that
merely stays alive or prints part of a boot log is not a passing test.

There is no deployment target yet, so continuous deployment would be premature.
Once a bootable artifact exists, tagged releases can publish images and build
provenance; real-hardware deployment should remain a separate, opt-in test lane.

### Lean development

Install [Elan](https://github.com/leanprover/elan), then run the repository-owned
check from the repository root:

```sh
./scripts/check.sh
```

Elan reads `lean-toolchain` and installs the exact Lean release automatically.
The check builds every default Lake target and verifies that the deliberately
invalid proof fixtures remain rejected. Lean warnings are errors for project
modules, so declarations containing `sorry` or `admit` fail the build. The
check also rejects unapproved `axiom`, `constant`, `unsafe`, and `extern`
declarations; required trusted-code boundaries must be documented and explicitly
allowlisted when they are introduced. GitHub Actions invokes the same script;
generated Lake output is kept under the ignored `.lake/` directory.

### Local CI commands

The pull-request workflow uses only these repository-owned entry points:

```sh
./scripts/check-markdown.sh
./scripts/check.sh
./scripts/build-image.sh
./scripts/run-image.sh
```

The first command requires Node.js/npm. Image building and QEMU prerequisites,
the exact Ubuntu 24.04 package versions used in CI, and emulator resource bounds
are listed in [the boot-image guide](docs/boot-image.md). CI first runs the
Markdown and complete Lean proof-integrity gates, then builds and boots the
image without KVM. It retains the ISO, debug ELF, symbol map, checksums, pinned
tool versions, and serial log for 14 days, including available diagnostics from
failed runs. Controlled negative fixtures ensure theorem, compiler, serial
protocol, guest-signal, and timeout failures cannot pass.

Tags matching `vMAJOR.MINOR.PATCH` additionally run the exact proof, build, and
QEMU gates, require a byte-identical double build, and publish experimental
release artifacts with checksums and GitHub provenance. The version policy,
artifact inventory, trusted-boundary warning, and download verification
commands are in [the boot-image guide](docs/boot-image.md).

## Roadmap

### Phase 0: foundations

- define the scope, threat model, target platform, and proof vocabulary;
- pin Lean, Lake, QEMU, linker, and cross-compilation dependencies;
- test the freestanding Lean/runtime boundary and record the architecture
  decision; and
- establish local commands that CI invokes without duplicating build logic.

### Phase 1: proved boot slice

- create a minimal bootable image and serial-console protocol;
- define the first abstract kernel state and operation;
- prove its key invariants and connect it to the boot demo; and
- run proof, build, and QEMU smoke checks on every pull request.

### Phase 2: capability microkernel core

- introduce kernel objects, capabilities, and address spaces;
- specify and prove authority-preservation properties;
- add memory allocation, mapping, IPC, and syscall boundaries one slice at a
  time; and
- expand adversarial model tests and emulator scenarios.

### Phase 3: system services

- move policy into isolated user-space services;
- explore verified storage, networking, and recovery components; and
- add hardware-backed test lanes without weakening deterministic QEMU CI.

## Contributing

The initial backlog is maintained in
[GitHub Issues](https://github.com/rudi-cilibrasi/leanos/issues). Before opening
a pull request:

1. link the issue or design question the change addresses;
2. distinguish proved properties from tested behavior;
3. document any new TCB assumption or unverified boundary;
4. run the same repository scripts used by CI; and
5. keep the change to one reviewable vertical slice.

Architecture-changing work should begin with a short issue or decision record.
Proofs are part of the implementation: changes that invalidate them should fix
or deliberately revise the associated specification in the same pull request.

## Current repository status

Today the repository contains its project charter, the Phase 1 architecture
boundary, a pinned Lean project, and repository hygiene and proof-build checks.
The issue tracker defines the bootstrap work. Until a milestone is linked here
with passing proof and emulator evidence, LeanOS should be described as an
experimental research project rather than a verified operating system.
