# ADR 0029: Refinement theorems for the spawn, loader and frame-check exports

## Status

Accepted, issue #570. Extends [ADR 0023](0023-one-export-refinement-ladder.md)
from one export to six.

## Context

ADR 0023 proved one rung-3 refinement: the C that the pinned toolchain emits
for `leanos_boot_transition`, read under a reviewed C-subset semantics, computes
the Lean definition on every input. Six newer exports are small and
security-critical, yet only oracle vectors and booted replay covered them:

| Export | Lean definition | Issue |
| --- | --- | --- |
| `leanos_spawn_syscall` | `SpawnSyscall.spawnSyscall` | #554 |
| `leanos_spawn_syscall_value` | `SpawnSyscall.spawnSyscallValue` | #554 |
| `leanos_loader_source` | `ChildLoader.loaderSource` | #555 |
| `leanos_loader_decide` | `ChildLoader.loaderDecide` | #555 |
| `leanos_frame_copy_check` | `NetworkSubject.frameCopyCheck` | #548 |
| `leanos_frame_port_check` | `DhcpSubject.framePortCheck` | #564 |

Their emitted C is larger than the boot adapter's. It takes up to six
arguments, uses more `lean.h` helpers, places join points inside nested
blocks, jumps backwards to them, and calls emitted helper functions. The spawn
syscall also calls a second generated export, the dispatcher table
`leanos_composite_dispatch`.

## Decision

### The subset grows; its meaning stays a reviewed reading of C11

`LeanOS/Refinement/CSubset.lean` adds:

- `uint8_t` parameters and results;
- the inline `lean.h` helpers `lean_uint64_dec_lt`, `_dec_le`, `_add`,
  `_sub`, `_land`, `_lor`, `_xor`, `_shift_left`, `_shift_right` and `_mod`,
  each given its `lean.h` body;
- calls `f(x, …)` on variables, given meaning by an explicit environment
  `Ext`;
- `goto` to a label anywhere in an enclosing block list, forward or backward.

The meaning of every construct is written in that one file. The extractor
`scripts/extract-generated-c.py` parses exactly that subset and rejects
everything else.

### Proofs go through a verified symbolic evaluator

Unfolding the semantics with `simp` on symbolic words did not scale to
`leanos_loader_decide`. `LeanOS/Refinement/CSymbolic.lean` runs a function's
AST on symbolic words. The result is a closed tree of conditions and result
words, which the kernel computes. `srun_sound` proves the tree sound against the
`CSubset` semantics, and `callWith_of_tree` lifts it to a call. Each
refinement proof then compares a small `if`-tree with the Lean definition case
by case. The meta tactics there (`csym_tree`, `csym_case`) only find terms.
The kernel re-checks every proof, so they add no trust (as with `kernel_rfl`).

### One module per export family, one drift row per function

| Module | Functions proved (C name) |
| --- | --- |
| `Refinement.SpawnSyscallC` | `leanos_spawn_syscall`, `leanos_spawn_syscall_value`, and helpers `l_LeanOS_SpawnSyscall_{syscallTag,canonical,familyToken,stateActor,isEdgeReply}` |
| `Refinement.ChildLoaderC` | `leanos_loader_source`, `leanos_loader_decide` |
| `Refinement.NetworkSubjectC` | `leanos_frame_copy_check`, helper `l_LeanOS_NetworkSubject_frameCopyDecide` |
| `Refinement.DhcpSubjectC` | `leanos_frame_port_check` (with `framePortDecide` inlined) |

`scripts/refinement-exports.tsv` lists every proved C function and its AST.
`build-image.sh` re-extracts each one from `build/boot/<module>.c`, the files
compiled into the images, and fails on any drift.

### Theorems and claims

Each export has a rung-3 theorem: for every fixed-width input, the call returns
`some` of the Lean definition (`*C_refines`). Where the Lean definition already
has a model theorem, the module composes the two:

- the loader pair returns the encoded reply of `ChildLoader.step`
  (`loaderC_refines_start`, `loaderC_refines_load`);
- the frame checks accept exactly when `fetchOk`/`sendOk` does and refuse
  non-holders;
- the spawn syscall's answer is a refusal or exactly one spawn-table edge's
  reply, so `spawnSyscall_refines`, `_rollback` and `_trace` hold of the emitted
  C.

The claim index has one refinement row per export, from
SC-SPAWN-SYSCALL-REFINEMENT to SC-FRAME-PORT-REFINEMENT. `tests/RefinementStatements.lean`
pins each statement.

### Negative fixtures

- `LeanOS.NegativeFixtures.ExportRefinement`: for every export, a mutated AST
  (one constant changed) and a mutated Lean witness (a dropped check) each
  disagree with the original on a concrete input. The disagreement is decided
  by kernel evaluation, so neither refinement statement can hold of the
  mutant.
- `tests/fixtures/refinement-mutants.tsv`: `drift` rows patch the emitted C of
  each export, and of two helpers, and the drift check must reject it. One of
  them uses a construct outside the subset. `claim` rows weaken each new claim
  statement, and the pinned contract must reject it. The unmutated claim
  fixtures must pass.

## TCB note

What the six refinement theorems leave trusted, exactly:

1. **The C-subset meaning** (`CSubset.lean`). This is a reviewed reading of
   C11 and of the `lean.h` helper bodies listed above, not a mechanized C
   standard.
2. **The extractor** (`scripts/extract-generated-c.py`). It must map the
   emitted text to the AST faithfully. Variable, label and callee names are
   copied verbatim.
3. **The C compiler and linker**, which turn the checked C text into machine
   code, and the **`uint64_t`/`uint8_t` calling convention** between the
   kernel's C and these functions.
4. **The dispatcher's C**, for the two spawn exports only. `DispatchSpec`
   assumes that the emitted `leanos_composite_dispatch` and
   `leanos_composite_dispatch_value` compute `CompositeDispatcher.dispatch` and
   `dispatchValue`. It is a hypothesis of the theorems, not proved here.

The **Lean compiler** is no longer trusted for what these functions compute.
The theorems are about the C it emitted, and the build checks that this C is
what gets compiled. It stays trusted for everything else it emits. The **Lean
kernel** is trusted as for every proof. The new claims use only `propext`,
`Classical.choice` and `Quot.sound`, with no `native_decide`.

Excluded from every new claim: the runtime shim, the boot path, QEMU,
hardware, the kernel's computation of the words it passes in, and every other
export.

## Consequences

- If the toolchain or a witness changes the emitted C, the image build fails
  until the AST is regenerated (`extract-generated-c.py --update`) and the
  proof is re-checked. Variable numbering changes when unrelated code in the same
  module changes, so editing `ChildLoader.lean`, `SpawnSyscall.lean`,
  `NetworkSubject.lean` or `DhcpSubject.lean` can require regenerating the AST.
  The proofs themselves usually need no edit.
- A new scalar export whose C stays in the subset gets a refinement theorem
  from its AST and `csym_refine`, plus simp lemmas for the callees.
