# ADR 0023: A refinement ladder for one generated export

## Status

Accepted, issue #470. Implemented for `leanos_boot_transition`.

## Context

No proved edge runs from the Lean model to the generated binary: the README
diagram draws it dashed, and every claim in `docs/security-claims.md`
excludes generated-code refinement. The smallest useful step is one export,
stated exactly and stopping at the export: `leanos_boot_transition`, the
scalar adapter `KernelTransition.bootTransition`. That adapter already
agrees with `transition` in Lean (`bootTransition_agrees`).

The generated C for it, from the pinned toolchain, is small: it uses two
`lean_uint64_dec_eq` calls, `if (x == 0)` on locals, one join point reached
by `goto`, and two `return`s. It allocates nothing and calls nothing else.

Two methods were considered for the step from Lean to C (rung 3):

1. **A C-subset semantics in Lean.** A deep embedding of exactly the C
   constructs the emitter uses. A checked-in extractor produces the AST from
   the generated `.c`, and the build fails if the emitted text drifts from the
   AST the proof covers. A proof then shows the AST's meaning equals the Lean
   definition.
2. **Lean IR translation validation.** Interpret the `Lean.IR` declaration
   and prove it equals the definition. A syntactic check would confirm that
   the C is the EmitC rendering of that IR. The IR→C step would then rest
   only on that syntactic check.

## Decision

Use **(1)**, the C-subset semantics.

- It states the result about the C text that is compiled, not about an
  intermediate form, so no IR→C step stays unchecked.
- The subset is tiny and fixed by what the emitter produces for scalar
  exports. Each construct's meaning is a reviewed reading of C11 written down
  in one Lean file.

The ladder for `leanos_boot_transition`:

1. **Lean executable semantics (proved).**
   - `KernelTransition.bootTransition_spec` states the adapter over the whole
     input domain: it accepts only `(0, 1)`, and every other word pair,
     including state words that encode nothing, is rejected.
   - `bootTransition_agrees` connects the adapter to `transition` on every
     model state. Its unused well-formedness hypothesis is removed: the adapter
     reads only the encoded phase.
2. **Generated-C differential evidence (tested).** The hosted oracle replays
   the generated C over the classification grid: every pair from
   {0, 1, 2, 2^64 − 1} for each argument, 16 vectors
   (`Oracle.bootTransitionClassVectors`). This runs in the ordinary and
   sanitized hosted modes.
3. **The emitted C refines the model (proved).**
   - `LeanOS.Refinement.CSubset` defines the subset and its meaning.
   - `LeanOS.Refinement.BootTransitionC.bootTransitionC` is the extracted AST.
   - `bootTransitionC_refines`: for every pair of 64-bit words, calling the
     AST returns `bootTransition`.
   - `bootTransitionC_refines_transition`: on every encoded model state the
     call returns the model's encoded result.
   - Both theorems use only the standard axioms.
   - `scripts/extract-generated-c.py --check` runs in `build-image.sh` on the
     generated `KernelTransition.c`. `scripts/test-extract-generated-c.sh`
     shows that a changed constant, a changed comparison operand, or a helper
     outside the subset all fail the check.

## TCB delta

These become trusted, with exact scope:

- **The C-subset meaning** in `LeanOS/Refinement/CSubset.lean`: declared
  `uint8_t`/`uint64_t` locals with conversion on assignment;
  `lean_uint64_dec_eq` as `a == b` (its `lean.h` definition); `if (x == 0)`;
  labelled blocks reached by `goto`; `return`. This is a reviewed reading of
  C11 for these constructs, not a mechanized C standard.
- **The extractor** `scripts/extract-generated-c.py`, which parses only that
  subset and rejects everything else.
- **The calling convention** that passes two `uint64_t` arguments and returns
  one stays a named assumption.

The theorem does not cover the runtime shim, the C compiler, the linker, the
boot path, QEMU, any other export, or `boot/kernel.c`. The README keeps its
dashed model→binary edge; this export gains a narrow proved annotation.

## Consequences

- A toolchain bump or a change to `bootTransition` that alters the emitted C
  fails the build until the AST is regenerated and the proof re-checked.
- Further exports can reuse the subset where their emitted C stays inside it;
  extending the subset needs a new reviewed construct and an update to this
  ADR.
