# ADR 0001: Phase 1 scope, threat model, and trusted base

- Status: Accepted
- Date: 2026-07-14
- Owners: LeanOS maintainers
- Supersedes: Nothing
- Related issues: [#2](https://github.com/rudi-cilibrasi/leanos/issues/2),
  [#4](https://github.com/rudi-cilibrasi/leanos/issues/4), and
  [#6](https://github.com/rudi-cilibrasi/leanos/issues/6)

## Context

LeanOS needs a narrow first milestone whose evidence cannot be mistaken for a
verified operating system. This record fixes the target, attacker model, proof
vocabulary, and initial trusted computing base before the boot and Lean runtime
experiments choose expensive implementation details.

Phase 1 is an experimental, single-core, x86-64 boot demonstration under QEMU.
It has no users, persistent data, network, or production deployment role.

## Decision

### Target and boot environment

The Phase 1 target is the x86-64 System V ABI on one emulated CPU. The reference
machine is QEMU's `q35` PC machine with software emulation (TCG), a serial
console, and no network device. The image boots through the QEMU-distributed
SeaBIOS firmware and GRUB 2's Multiboot2 path. The image build will pin the
exact QEMU machine version, QEMU, SeaBIOS, GRUB, compiler, assembler, and linker
versions rather than relying on host defaults.

This choice provides a conventional, headless path that runs on GitHub-hosted
Linux runners without KVM. It deliberately accepts a larger boot TCB for the
first slice instead of making firmware or bootloader verification a prerequisite.
ADR 0002, produced by issue #4, may choose the language and ABI boundary around
Lean-generated computation. Changing the target machine or boot path requires
superseding this record and updating the TCB inventory.

The milestone is complete only when one repository-owned command builds a
versioned image and another boots it with a bounded timeout. The guest must:

1. reach a documented boundary around a Lean-defined state transition;
2. emit a versioned serial record containing its input, result, and final status;
3. request a machine-readable QEMU success exit; and
4. produce identical observed results on repeated runs from the same inputs.

### Phase 1 threat model

#### Protected assets

- **A1 — transition integrity:** the modeled state transition returns the result
  defined by its Lean specification for the supplied modeled input.
- **A2 — invariant preservation:** an accepted transition preserves the named
  well-formedness invariant proved for the abstract state.
- **A3 — evidence integrity:** CI does not report success unless proof checking,
  image construction, the complete serial protocol, and the guest success signal
  all succeed for the same source revision.
- **A4 — artifact identity:** an image and its logs can be associated with the
  source revision and pinned build inputs that produced them.

#### Trusted actors

Repository maintainers and GitHub administrators are trusted to review source,
protect repository settings and credentials, select pinned dependencies, and
publish intended revisions. The GitHub Actions service and runner operator are
trusted to execute the declared workflow and report its result faithfully.

#### Attacker capabilities

The modeled attacker may submit arbitrary pull-request source changes and
arbitrary values to the exported modeled transition. Inputs may be malformed or
request an unsupported operation. The attacker may try to omit, truncate, forge,
or reorder guest serial messages; make the guest hang or crash; or make a
host-side emulator process merely remain alive.

The bounded Phase 2 machine attacker also controls CPL3 instruction bytes and
saved general-purpose registers. In the fast-entry-denial slice it may execute
raw `SYSCALL` or `SYSENTER`, attempt to exploit inherited SCE or stale target
MSRs, and present words resembling a subject, CR3, stack, survivor, vector, or
error code. Those words are not authority inputs. Only the hardware-derived
frame plus protected current-subject, address-space, entry-stack, and live
control state may produce a contained denial; any mismatch is fail-stop.

The harness must reject those integration failures, and the transition must give
invalid modeled input an explicit, state-preserving result. Untrusted pull-request
code receives no repository write token or long-lived secret.

#### Excluded attacks and properties

Phase 1 does not model or claim resistance to:

- malicious or compromised maintainers, GitHub infrastructure, runners, or
  dependency distribution services;
- compromised firmware, GRUB, QEMU, compiler, linker, assembler, Lean toolchain,
  generated code, foreign code, or physical hardware;
- side channels, speculative execution, timing leakage, denial of service, or
  resource-exhaustion beyond the smoke-test timeout;
- DMA behavior outside the finite Phase 2 q35 quarantine model and its explicit
  device-control assumption; device assignment, IOMMUs, devices other than the
  selected manifest/console/exit path, networking, storage services, interrupts,
  SMP, concurrency, userspace, or hostile physical access;
- complete architectural-state isolation: Phase 2 denies representative x87,
  MMX, SSE, SSE2, and AVX use but does not enumerate every XSAVE component,
  opcode, exception-priority interaction, or physical CPU;
- binary reproducibility until it is separately measured, or correspondence
  between machine code and Lean semantics beyond tested boundary behavior; or
- memory safety, capability safety, isolation, information-flow security,
  liveness, boot authenticity, secure boot, rollback protection, or production
  suitability.

### Claims and evidence

Every Phase 1 correctness statement must use one of these terms:

- **Specified:** a behavior is defined by a named Lean definition or versioned
  interface document. A specification alone supplies no correctness evidence.
- **Proved:** a named Lean theorem, checked with the pinned toolchain and without
  project-added axioms or admitted obligations, establishes a property of a
  named model under stated preconditions. The claim does not extend to generated
  code, the runtime, foreign code, or hardware unless a separate refinement proof
  says so.
- **Tested:** a named repository command observed expected behavior for stated
  inputs in a stated environment. Testing neither proves all inputs nor verifies
  the compiler, boot chain, emulator, or hardware.
- **Trusted:** a component or assumption is outside the proof and must behave as
  documented for a claim to carry across that boundary.

The initial named claims are:

| Claim | Model and assumptions | Required evidence |
| --- | --- | --- |
| C1: transition determinism | The Phase 1 Lean state/command/result model; identical modeled state and command | A Lean theorem that any two evaluations have equal results |
| C2: invariant preservation | The same model; its named well-formedness predicate and operation preconditions | A Lean theorem that accepted execution preserves well-formedness |
| C3: invalid-input stability | The same model; inputs classified as invalid by its validator | A Lean theorem or definitional proof that rejection leaves modeled state unchanged, plus examples |
| C4: boundary exercise | The selected ADR 0002 boundary and all components in the TCB inventory | A build plus bounded QEMU test observing the exact input and result in the complete serial protocol |
| C5: CI evidence integrity | GitHub and runner assumptions, immutable action references, pinned tools, and repository scripts | A workflow in which proof and build gates precede a smoke test that requires both serial completion and guest exit success |

C1–C3 are intended proof claims about a model. C4–C5 are tested integration
claims. Compilation, linking, a QEMU boot, or C4 passing must never be described
as proving that the binary implements the Lean model.

### Trusted computing base and assumptions

The inventory below is auditable even where issue #4 has not selected the final
boundary. Exact versions and artifacts will replace the placeholders during the
corresponding implementation issues.

| Component | Why it is trusted | Failure impact | Owner/evidence |
| --- | --- | --- | --- |
| Lean kernel and pinned Lean/Lake toolchain | Elaborates and checks C1–C3; compiler may generate boundary code | A bug can accept a false theorem or produce code with different behavior | Issues #3–#5; toolchain file and proof logs |
| Phase 1 Lean definitions and theorem statements | They define the model and the property actually proved | A weak or incorrect model makes a true theorem irrelevant | Source review and named claims in this ADR |
| Lean runtime and generated C/native code, if selected | Implements allocation, initialization, exceptions, and execution outside the proved model | Runtime or code-generation faults can violate boundary behavior | Issue #4 experiment and ADR 0002 |
| Boot assembly and foreign C/Rust, if selected | Establishes CPU state and bridges firmware, ABI, runtime, serial, and exit interfaces | ABI or memory errors can forge output, corrupt state, or crash | Issue #4/#6 source and tests |
| Interrupt descriptor/frame adapter | Loads the IDT/TSS, clears AC/DF, selects entry stacks, decodes x86 frame words, and bridges the generated manifest oracle | A descriptor, shape, bounds, latch, or ABI mismatch can authorize the wrong handler/context | `LeanOS.InterruptEntry`, `scripts/check-entry-policy.sh`, runtime snapshot, and QEMU logs |
| Extended-state denial boundary | Reads CPUID and CR0/CR4, normalizes controls, routes vectors 6/7, invokes the generated scalar gate, decodes the selected probe, cleans up A, and restores B | A stale snapshot, wrong vector/binding, incomplete opcode inventory, or restore bug can expose shared processor state or misclassify a kernel fault | `LeanOS.ExtendedState`, `docs/extended-state-denial.md`, policy reports, decoded snapshots, and five QEMU transcripts |
| PCI snapshot and device-control boundary | Completely enumerates the selected q35 bus after firmware, clears and reads back every present function's PCI Command bus-master bit before CPL3, and gives that bit the architectural effect assumed by the finite quarantine model | An omitted function, optional-absence/read-failure ambiguity, stale read-back, firmware/device disobedience, incorrect Command semantics, or C/final-binary mismatch can permit DMA despite a valid model result | `LeanOS.DMAQuarantine`, `boot/kernel.c`, `docs/dma-quarantine.md`, construction TSV, and mandatory `LEANOS/15 DMA` QEMU records; tested boundary, not proved refinement |
| Fast privilege-entry denial boundary | Reads the selected AMD CPUID contract, writes and rereads EFER/STAR/SYSENTER MSRs, routes the exact vector-6 denial, invokes the scalar classifier, cleans up A, and restores B through the sole user-return gate | Inherited SCE, a stale target/stack, wrong exception semantics, a hidden fast-entry opcode, or stale binding can bypass the reviewed `int 0x80` entry or misclassify a kernel fault | `LeanOS.PrivilegeEntryControl`, `docs/privilege-entry-control.md`, hosted 32-vector corpus, final-ELF inventories, decoded snapshots, and two QEMU transcripts |
| Compiler, assembler, linker, and linker script | Translate and lay out the executable; no verified compilation claim is made | The image may not correspond to reviewed source | Pinned versions, map file, and build logs |
| GRUB 2 and Multiboot2 implementation | Loads the image and passes boot information | It can load or initialize the wrong bytes/state | Pinned package/artifact and boot test |
| SeaBIOS | Initializes the emulated platform and starts GRUB | It can alter platform state or fail before the kernel boundary | Version reported with the QEMU build |
| QEMU `q35`, x86-64 TCG, serial, and debug-exit models | Execute the image and provide observed integration evidence | Emulator/model bugs can create false passing or failing observations | Pinned QEMU/machine versions and invocation log |
| x86-64 ISA, System V ABI, Multiboot2, and selected device contracts | Define behavior assumed by low-level code | Specification mismatch invalidates the bridge | Cited versions in ADR 0002/build documentation |
| GitHub Actions service, runner image, and referenced actions | Fetch and execute gates and preserve their reported status | Compromise can forge evidence or artifacts | Least-privilege workflow, pinned actions, logs |
| Host OS, filesystem, shell, build scripts, and dependency archives | Supply and execute the build environment | Nondeterminism or compromise can change the artifact | Repository scripts, checksums, and tool manifest |
| Maintainers and repository controls | Choose source, models, dependencies, settings, and releases | A trusted actor can weaken claims or replace evidence | Branch protection, history, and reviewable changes |
| Physical CPU and devices, if tested later | Implement the assumed ISA and device behavior | Hardware errata can violate assumptions | Outside Phase 1; separate evidence lane required |

No row is verified by Phase 1. A checksum establishes identity, not correctness.
The runtime/foreign-code rows must be made concrete by ADR 0002 before issue #6
connects the transition to the image.

## Milestone boundary

If C1–C5 have their required evidence, LeanOS may say:

> For a named abstract transition, Lean checked determinism, invalid-input
> behavior, and preservation of a named invariant under documented assumptions.
> A pinned experimental x86-64 image was integration-tested under a pinned QEMU
> configuration to exercise that transition and emit the expected result.

It may not say that LeanOS, its kernel binary, boot chain, compiler, runtime,
QEMU, or hardware is verified; that the theorem establishes security or memory
safety; or that the image is safe for production use.

## Consequences

- Issues #3–#8 have a stable target and vocabulary for their documentation.
- Issue #4 must compare at least two Lean/foreign boundaries and publish ADR
  0002 with concrete ABI, runtime, allocation, exception, and initialization
  assumptions before issue #6 relies on one.
- Issue #5 must attach C1–C3 to exact definitions and theorem names.
- Issues #6–#8 must preserve the distinction between proof logs and integration
  evidence and record the exact TCB versions used.
- Firmware and bootloader verification, real hardware, and stronger security
  properties remain explicit future work rather than implicit milestone claims.

## Revisit conditions

Supersede this ADR if evidence from issue #4 rules out the selected boot path, a
different architecture or firmware becomes the reference target, the first
transition needs devices or concurrency excluded here, or a claim crosses a TCB
boundary without a corresponding refinement argument.
