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
| Emulator | Boot headlessly in QEMU with a timeout and serial assertions | Planned |
| Artifacts | Upload the image, symbol map, serial log, and checksums | Planned |
| Release | Publish versioned, reproducible images with provenance | Future |

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
invalid proof fixture remains rejected. GitHub Actions invokes the same script;
generated Lake output is kept under the ignored `.lake/` directory.

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
