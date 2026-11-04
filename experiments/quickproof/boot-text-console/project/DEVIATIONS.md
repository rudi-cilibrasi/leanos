# Deviations of the boot-text-console project

The theorems are about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. `volatile` is defined away (`DEFS=(-Dvolatile=)` in `quickproof.conf`)

`include/boot_text_console.h` writes the geometry through a `volatile` pointer
and keeps the console's cell pointer and its `enabled`/`busy` flags `volatile`.
The qualifier stops the compiler from reordering or eliding those accesses,
because the cells are device memory and the console is used from interrupt
context. VST has no rule for volatile accesses (`qp audit` lists 19). In one
thread, under CompCert's semantics of a non-volatile object, a volatile access
loads or stores the same value. The theorems therefore say nothing about
compiler reordering, device side effects of the stores, or reentrancy.

## D2. A wrapper unit (`patch/console_unit.c`)

The header's functions are `static`. The unit includes the header unchanged
and gives the three functions the laws call external names (`console_parse`,
`console_enable`, `console_putc`). The kernel also calls `boot_text_disable`,
which `boot_text_enable` calls and which is proved here too. Each wrapper only
forwards its arguments, and its body is proved like every other function.

## D3. The Lean export is linked as a model (`patch/lean_export_model.c`)

`leanos_boot_text_surface` is compiled from `LeanOS.BootTextConsole.checkRaw`.
Its emitted C uses `goto` join points, which VST does not support, so the
program links a 25-line C model instead. Two proofs tie the model to the export:

- Coq (`proof/src/proof/ModelProof.v`, `body_surface` and `valid_geo_iff`): the
  model returns 1 exactly when
  `kind = 2 ∧ bits = 16 ∧ address = 753664 ∧ 0 < width ≤ 160 ∧ 0 < height ≤ 64 ∧
  pitch mod 2 = 0 ∧ 2·width ≤ pitch ∧ pitch ≤ 512`, and 0 otherwise.
- Lean (`LeanOS/Refinement/BootTextConsoleC.lean`, `bootTextSurfaceC_spec`,
  claim SC-BOOT-TEXT-SURFACE-REFINEMENT): the emitted C returns 1 exactly under
  the same conjunction over the naturals, and 0 otherwise. The build checks
  that the emitted C is the AST this theorem is about.

Two steps remain trusted:

- that the two conjunctions are the same, a reading of two printed statements;
- that both functions take six `uint64_t` arguments and return one in the
  same way, the calling-convention assumption of every rung-3 theorem
  (ADR 0029).

## D4. A shim for the generated `boundary-abi.h` (`patch/boundary-abi.h`)

The generated header declares every export. The shim declares only
`leanos_boot_text_surface`, with the generated prototype. Its parameter and
result types are also fixed by the AST that the Lean refinement theorem covers.

## Not deviations, but limits of the laws

- The window is an object of exactly `height * pitch` bytes. The kernel passes
  the fixed address `0xb8000`. That the aperture is mapped, owned and decoded
  there is a boot-time assumption (`docs/early-text-console.md`).
- `boot_text_parse` is given the exact length of its buffer as `available`. The
  kernel passes the distance to `BOOT_ACCESSIBLE_LIMIT`, which covers at least
  the handoff.
- Partial correctness: termination is not claimed, though every loop of the
  header is bounded.
