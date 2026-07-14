# ADR 0002: Restricted generated-C boundary for Phase 1

- Status: Accepted
- Date: 2026-07-14
- Related issues: [#4](https://github.com/rudi-cilibrasi/leanos/issues/4),
  [#5](https://github.com/rudi-cilibrasi/leanos/issues/5), and
  [#6](https://github.com/rudi-cilibrasi/leanos/issues/6)

## Context

Phase 1 needs to invoke a Lean-defined computation after x86-64 boot without
implying that compilation or execution verifies the resulting binary. We tested
two boundaries with the pinned Lean 4.32.0 compiler. Run both experiments with:

```sh
./scripts/check-boundary-experiments.sh
```

The script regenerates every artifact under the ignored `build/` directory and
fails unless both computations return `0x55 XOR 0x0f = 0x5a` (decimal 90).

## Evidence

### Option A: restricted generated C with a freestanding shim

`experiments/freestanding-boundary/Boundary.lean` exports a `UInt64`-only
function. Lean generates C, the host C compiler creates function-level sections,
and the linker garbage-collects initialization and boxed wrappers. A 12-line
assembly entry and one C implementation of Lean's `UInt64.xor` primitive make a
static ELF with no unresolved symbols or libc dependency. Executing it reaches
the Lean-generated function and exits zero only when it returns `0x5a`.

Observed on Ubuntu 24.04 with GCC 13.3.0 and GNU ld 2.42:

| Artifact | Size |
| --- | ---: |
| Generated `Boundary.c` | 1,958 bytes |
| `Boundary.o` before section collection | 12,400 bytes |
| Static `direct.elf` | 9,096 bytes |

The first success point is a freestanding, allocation-free exported function.
The first known failure boundary is any operation whose reachable generated C
requires an unimplemented Lean runtime symbol. The Phase 1 image build must
reject unexpected undefined symbols instead of silently growing the shim.

### Option B: hosted Lean runtime

`experiments/hosted-boundary/Hosted.lean` uses ordinary `IO`, formatting, and
the full native runtime. `leanc` produces a runnable executable that prints
`LEANOS-HOSTED result=90`.

The observed executable is 4,203,568 bytes and dynamically requires glibc,
pthread, dl, rt, and libm. Its first success point is a normal Linux process.
Its first freestanding failure point is the absent OS surface for allocation,
threads, dynamic loading, clocks, math, standard I/O, and process startup.
Porting that surface would be a larger and less auditable Phase 1 TCB.

These sizes are observations, not reproducible-byte claims. Lean is pinned by
`lean-toolchain`; issue #6 must pin the C compiler, assembler, linker, GRUB,
SeaBIOS, and QEMU before making artifact-identity claims.

## Decision

Phase 1 will use Option A. Issue #5 will expose one total, allocation-free
transition over fixed-width scalar values. Issue #6 will compile that export to
C and call it from the minimal assembly/C boot layer selected by ADR 0001.
Reachable runtime primitives will be implemented as small foreign shims, kept in
a reviewable inventory, and tested against the Lean model. The build will use
function/data sections, garbage collection, and an undefined-symbol gate.

The full Lean runtime remains a viable later option when richer data or effects
justify its initialization and operating-system services. It is not selected
for the first boot slice.

## Trusted boundary

The following are trusted for the boundary behavior:

- Lean elaboration, code generation, generated C, and the selected export ABI;
- the C compiler, assembler, linker, linker script, and section collection;
- System V x86-64 calling convention and fixed-width C integer representation;
- boot assembly and every reachable foreign primitive (currently only XOR);
- the manual agreement between the Lean primitive and its C implementation;
- firmware, GRUB, QEMU, and hardware assumptions listed in ADR 0001.

The restricted subset forbids allocation, exceptions, `IO`, closures crossing
the ABI, and runtime initialization in the boot-reachable call graph. Adding a
primitive or relaxing a restriction changes the TCB and requires an inventory
update plus focused boundary tests.

## Claims

The source computation is **specified** by the Lean definition. The experiment
is **tested** to compile, link, execute, and return one expected value. The
compiler, generated C, shim, ABI, and execution platform are **trusted**. No
refinement theorem connects generated code to Lean semantics, so neither this
experiment nor a future QEMU success proves binary correctness.

Issue #5's model proofs will establish properties only of its Lean definitions.
Issue #6 must report invocation of the exported transition as integration-test
evidence and must not extend those proofs across this boundary.

## Consequences and failure modes

- The first transition stays deliberately scalar and allocation-free.
- Compiler output changes can add runtime calls; the symbol gate makes this a
  visible failure rather than an implicit TCB expansion.
- Linker garbage collection is correctness-critical: retained initialization or
  boxed paths would require runtime services not present at boot.
- ABI mismatch, miscompilation, a faulty shim, or boot memory corruption can
  produce an incorrect result despite all Lean proofs passing.
- The experiment runs as a Linux ELF only to exercise the ABI cheaply. It does
  not test Multiboot2, privileged CPU setup, serial I/O, or QEMU; issue #6 owns
  those integration points.
