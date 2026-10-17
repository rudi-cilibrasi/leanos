# ADR 0029: Refinement theorems for the spawn, loader and frame-check exports

## Status

Accepted, issue #570. Extends [ADR 0023](0023-one-export-refinement-ladder.md)
from one export to six.

Amended 2026-10-17 (#575): the two spawn-syscall exports are gone. The
`spawn-child` and `spawn-loader` kernels no longer hold a token of the fixed
spawn table; they decide the family with the spawn allocator's exports
(`leanos_spawn_allocator_*`, `LeanOS.SpawnAllocatorWords`), and the fixed table,
`LeanOS.SpawnSyscall`, `leanos_spawn_syscall` and `leanos_spawn_syscall_value`
were deleted. With them went `Refinement.SpawnSyscallC`, the claims
SC-SPAWN-SYSCALL-REFINEMENT and SC-SPAWN-SYSCALL-VALUE-REFINEMENT, their drift
rows in `scripts/refinement-exports.tsv`, and their mutants. The four remaining
exports keep their proofs unchanged. The allocator's exports have no rung-3
proof yet; their evidence is `syscall_spec`/`kernel_spec` (rung 1, for every
input) and the hosted spawn-allocator corpus (rung 2).

Amended 2026-10-17 (#593): the allocator's seven exports now have rung-3
proofs, by the method below, in `Refinement.SpawnAllocatorC`. The pinned
toolchain emits each export and each of the 31 scalar functions they call
(`stepReply`, `decideW`, `canonical`, …) as its own C function of
`SpawnAllocatorWords.c`, all inside the subset, so no Lean refactoring and no
new subset construct was needed. All 38 functions have drift rows. The proof
is compositional: one theorem per C function, each callee resolved by the
theorem of its own AST (see "Composing many emitted helpers" below).

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
| `Refinement.ChildLoaderC` | `leanos_loader_source`, `leanos_loader_decide` |
| `Refinement.NetworkSubjectC` | `leanos_frame_copy_check`, helper `l_LeanOS_NetworkSubject_frameCopyDecide` |
| `Refinement.DhcpSubjectC` | `leanos_frame_port_check` (with `framePortDecide` inlined) |
| `Refinement.SpawnAllocatorC` (#593) | `leanos_spawn_allocator_seed`, `_syscall`, `_syscall_value`, `_syscall_next`, `_kernel`, `_kernel_value`, `_kernel_next`, and the 31 helpers they call (`l_LeanOS_SpawnAllocatorWords_*`, `l_LeanOS_SpawnAllocatorBoot_*`) |

`scripts/refinement-exports.tsv` lists every proved C function and its AST.
`build-image.sh` re-extracts each one from `build/boot/<module>.c`, the files
compiled into the images, and fails on any drift.

### Composing many emitted helpers (#593)

The spawn allocator's exports reach their 31 helpers through call chains up
to five calls deep (`syscallNext`, `stepNextWord`, `stepReply`, `decideW`,
`resolveControlW`, `childWordAt`). Proving each export with every callee
inlined would put the whole decision into one symbolic tree. Instead:

- `SpawnAllocatorC.helper?` maps a callee's arity and C name to its extracted
  AST, and `linkAt ext depth` resolves such a call by running that AST with the
  helpers linked one call less deep. `link ext` is `linkAt ext 5`, deeper
  than every chain, so every helper call resolves to its AST.
- A helper that calls helpers at most `k` calls deep has a theorem
  `*C_refines` under `linkAt ext (n + k)`, and its C name answers its Lean
  definition in `linkAt ext (n + k + 1)` (`link_*`). Each proof is one
  `csym_refine` over that function's own small tree, with its callees
  rewritten by their `link_*` theorems.
- Each export's theorem holds under `link ext`, for every `ext`: the exports
  call nothing outside their module.

`csym_close` also reduces `false = true`: a case on a `Bool` atom can rewrite
the atom itself (needed by `decideW`, whose checks are `Bool` helpers).

### Theorems and claims

Each export has a rung-3 theorem: for every fixed-width input, the call returns
`some` of the Lean definition (`*C_refines`). Where the Lean definition already
has a model theorem, the module composes the two:

- the loader pair returns the encoded reply of `ChildLoader.step`
  (`loaderC_refines_start`, `loaderC_refines_load`);
- the frame checks accept exactly when `fetchOk`/`sendOk` does and refuse
  non-holders;
- the spawn allocator's exports (#593), called as the kernel calls them,
  compute the decode–step–encode specification on every input
  (`syscallWordsC_spec`, `kernelWordsC_spec`, through
  `SpawnAllocatorBoot.syscall_spec` and `kernel_spec`), and the seed export
  gives the seed's words (`seedWordsC_eq`). With `seed_refines` those are the
  encoded family seed for every boot plan (`seedWordsC_spec`); that last step
  depends on `native_decide` through the boot plan's q35 platform, so it is
  kept out of the claim.

The claim index has one refinement row per export, from
SC-LOADER-SOURCE-REFINEMENT to SC-FRAME-PORT-REFINEMENT (the two spawn-syscall
rows were removed with their exports, #575), and two for the spawn allocator
(#593): SC-SPAWN-ALLOCATOR-REFINEMENT (each of the seven exports computes its
Lean definition on every input) and SC-SPAWN-ALLOCATOR-SPEC-REFINEMENT (the
composition with the specification). `tests/RefinementStatements.lean` pins
each statement.

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
- For the spawn allocator (#593): AST mutants of `seedC`, `decideWC` and
  `syscallC`, and a Lean syscall that forgets the parent-only rule, each
  disagree with the original on a concrete input, run with the linked
  helpers. Drift rows patch all seven exports and three helpers (three swap a
  callee, two leave the subset), and two `claim` rows weaken the two new
  claims.

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
4. **The dispatcher's C**, for the two spawn-syscall exports only (removed in
   #575). `DispatchSpec` assumed that the emitted `leanos_composite_dispatch`
   and `leanos_composite_dispatch_value` compute `CompositeDispatcher.dispatch`
   and `dispatchValue`. The spawn allocator's exports (#593) call only
   helpers of their own module, each proved from its own AST, so their
   theorems assume no other C.

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
  module changes, so editing `ChildLoader.lean`, `NetworkSubject.lean`,
  `DhcpSubject.lean` or `SpawnAllocatorWords.lean` can require regenerating the
  AST (for the spawn allocator, all 38 rows of its module).
  The proofs themselves usually need no edit.
- A new scalar export whose C stays in the subset gets a refinement theorem
  from its AST and `csym_refine`, plus simp lemmas for the callees.
