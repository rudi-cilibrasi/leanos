# ADR 0020: Assurance for the device-program executor

## Status

Accepted. Resolves the research question in issue #451. Amended by
issue #494 (below): option 1 is implemented, and the assurance argument for
the generated executor no longer rests on fuzzing.

## Context

The device-program theorems (`LeanOS/DeviceProgramConfinement.lean`) are
stated about `LeanOS/Wifi/Sim.lean`, while the Qotom runs
`hardware/wifi/wifi-exec.h`: about 300 lines of runtime-free C with one
`switch` interpreter, no allocation, and effect hooks. The only bridge was
`leanos-wifi-xcheck`, one hand-written computation-only program.

Auditing the executor for the confinement work (#447) showed that the bridge
was too weak. The previous simulator disagreed with the C executor on every
malformed input it met: it had no MMIO window or alignment check, mapped
unknown ALU sub-opcodes to arithmetic shift and unknown branch conditions to
signed `≥`, did not bound `blobStream32`, accepted any `memLoad`/`memStore`
width, ignored out-of-range register fields, and was a `partial def`, so no
theorem could mention it. The cross-check program never reached those paths.

Three options were considered.

1. **Generate the executor from Lean** through the restricted generated-C
   boundary (ADR 0002). That boundary is scalar-only and allocation-free: the
   first failure point is any operation whose generated C needs a Lean
   runtime symbol. The executor reads a byte image, owns 256 KiB of mutable
   scratch, a register file and a return stack, and performs effects through
   hooks whose results feed later steps. Expressing that in the boundary
   subset needs a new design: an `@[extern]` state interface for image,
   scratch and registers whose purity the Lean model must justify, and a
   proof that `Sim.exec` equals the exported step over that interface. This
   is the right long-term shape, but it is a project, not a change.
2. **Prove refinement against a C semantics.** The repository has no C
   semantics; hand-modelling the C step function would itself be an
   unchecked translation, and a mechanised one is a larger research effort
   than option 1.
3. **Differential fuzzing.** Cheap, independent of both options, and useful
   whichever is chosen later.

## Decision

Adopt option 3 now as a regression gate, and keep option 1 as the planned
path to remove the C/Lean divergence.

* `Sim.step` is total and mirrors `wifi-exec.h` check for check, in the same
  order and with the same status codes (`bad-offset`, `bad-opcode`, `policy`,
  …), so the confinement theorems are about the simulator the tests run.
* `leanos-wifi-fuzz` (`tests/WifiFuzz.lean`) generates seeded random
  programs as raw instruction words — including unknown opcodes and
  sub-opcodes, out-of-range registers, misaligned and out-of-window offsets,
  bad blob and scratch ranges, stack over/underflow, runaway branches, and
  random version-1/2/3 headers and policies — plus short *gadgets* that load
  a boundary value and use it at once (last scratch byte, FIFO end,
  `INT32_MIN / -1`, shifts by 30–33, window edge).
* `hardware/wifi/fuzz-runner.c` runs the same images through `wifi_exec` with
  the same deterministic device model. Each image yields one line: status,
  code, all 16 registers, and hashes of the prints, the device-effect trace
  and the whole scratch RAM. The two files must be byte-identical.
* The fuzzer's power is checked too: `scripts/check-device-programs.sh`
  applies each mutant in `tests/fixtures/wifi-exec-mutants.txt` (off-by-one
  bounds, a dropped policy check, wrong signedness, a removed overflow guard,
  …) to a copy of the executor and fails unless the fuzzed corpus exposes it.

## Evidence

* 5,000 programs (seed 0x2545F491) and 3,000 (seed 451, the CI gate): no
  disagreement. The CI corpus reaches every status: halt, fail, bad-pc,
  bad-offset, bad-opcode, stack, step limit, bad-blob, bad-mem and policy.
* Before gadgets, 4 of 15 mutants survived (the arithmetic-shift clamp, the
  scratch-end bound, `INT32_MIN / -1`, the FIFO-end bound); with them, 15 of
  15 are caught, one of them as a divide-by-zero trap in the runner.
* The gate takes about 25 s on the development machine.

## Consequences

* Agreement between `wifi-exec.h` and `Sim` remains **tested, not proved**;
  `docs/security-claims.md` keeps executor refinement as an exclusion for the
  device-program claims.
* Any change to either executor must keep the corpus identical and the
  mutants caught; a new check in one executor without the other fails CI.
* Revisit option 1 when the generated-C boundary gains a checked interface
  for mutable byte buffers, or before device programs run on behalf of kernel
  subjects (#449), whichever comes first.

## Amendment (issue #494): the generated executor

The trigger above fired when the `device-service` image began running
`wifi-exec.h` on behalf of subject 1 (#449 stage 2), so option 1 is now
implemented, as the design option 1 sketched: a Lean step function over an
`@[extern]` state interface, and a proof that it is `Sim.step`.

### Design

* `LeanOS/Wifi/Exec.lean` defines `Exec.step`, one instruction of the
  executor, against a class `Hooks τ` of named primitives: image and policy
  constants (`window`, `blobWord`, `polSink`, `polDescStart`, …), control
  state (`pcOk`, `fetch`, `advance`, `jump`, `call`, `ret`, stack full and
  empty), the register file, 1/2/4-byte scratch loads and stores, and the
  device effects (MMIO, configuration read/write/update, `phys`, delay,
  print), plus `done`, which ends the step with its status. Everything else —
  every register, window, alignment, blob, scratch, stack, sub-opcode and
  policy check, the address-sink and descriptor-map loops, the ALU and
  branch tables, and the bounded transfer loops — is Lean code over
  `UInt32`/`UInt64`.
* **Token discipline.** Each hook on mutable state takes the current token
  and returns the next; the value it reads is that token. The compiler can
  therefore neither reorder, merge nor drop hook calls: their order in C is
  their order in Lean. Hooks on immutable image data are plain functions.
* **Generated C.** At `τ := UInt64` the hooks are `@[extern]` C functions
  (`wifi_gen_*`), and `leanos_device_program_step` is the compiled step,
  specialized to them: allocation-free fixed-width C, inner loops compiled as
  `goto` loops, constants inline (`compiler.extract_closed` off, so no module
  initializer is needed). Opcode, ALU and branch dispatch are balanced trees
  of `<` tests (`Exec.exec_tree` proves the tree equals the opcode `match`),
  because a C compiler may lower a chain of `==` tests to a jump table, an
  indirect branch the entry-stack gate rejects.
* **Hooks in C.** `hardware/wifi/wifi-gen-exec.h` implements each hook as
  one direct reading or update of the existing executor state
  (`struct wifi_vm`, `wifi_scratch`) or one call of the existing `WH_*`
  device hooks, and `wifi_gen_resume`, the step loop. Image parsing and
  `wifi_start` are unchanged.
* **Descriptor map.** A scratch store that touches a declared region is
  checked against the scratch it *would* produce: the scan reads words
  through an overlay of the pending store, so the store happens only after
  the policy accepts it (the handwritten executor stores, checks and
  restores). Stores and FIFO input outside every region are not re-scanned;
  the frame lemma `ExecRefinement.descOk_frame` shows this agrees with
  `Sim`'s full re-check on every machine whose map already holds only
  scratch pointers, which every run maintains (`loop_descOk`).

### The assurance argument

* `ExecRefinement.instHooksSt` reads every hook over a simulator `Machine`
  (the program, the device model and the machine fields `Sim.step` uses).
* `ExecRefinement.step_eq` (restated as
  `DeviceProgramExecutor.generated_step_eq`): for every program the image
  parser accepts (`WF`: blob, sink and descriptor tables that fit 32 bits,
  regions inside scratch) and every machine a run reaches (`Inv`: scratch of
  the executor's size and, under a declared policy, a descriptor map that
  holds only scratch pointers), `decode (Exec.step …) = Sim.step p d m`.
* `run_eq` lifts this to whole runs (on devices whose bus address of
  scratch is fixed, as on every executor), so `run_confined`,
  `run_declared_confined` and `run_declared_descriptors` hold of the
  generated executor (`run_confined_generated`, …). The proofs use only the
  standard axioms (no `native_decide`, no `bv_decide`).
* What remains trusted is named: the Lean compiler and the C compiler, as
  for every generated boot export (ADR 0002); and that each C hook in
  `wifi-gen-exec.h` implements its Lean reading, each a few lines of state
  access. No refinement proof of the generated C is claimed (refinement
  ladder).

### Fuzzing is now a regression test

`scripts/check-device-programs.sh` runs the fuzz corpus through all three
executors — `Sim`, the handwritten `wifi-exec.h` and the generated one
(`scripts/check-generated-executor-host.sh`, the hosted generated boundary
`device-program-step`) — and requires identical summaries. During the
transition this diffs the generated executor against the handwritten one;
once the handwritten interpreter is deleted, the corpus stays as a regression
test. Its power over the trusted part is checked too: each hook mutant in
`tests/fixtures/wifi-gen-exec-mutants.txt` must be caught. The same script
links the generated step freestanding with the boot code-generation flags
and requires no undefined symbol and no indirect branch.

### Evidence for the generated executor

* 3,000 fuzzed programs (seed 451): `Sim`, `wifi-exec.h` and the generated
  executor agree; 13 of 13 hook mutants and 31 of 31 executor mutants are
  caught. The hosted boundary also passes under ASan/UBSan.
* The freestanding link of `leanos_device_program_step` with the C hooks
  (`-nostdlib --gc-sections`, `-ffreestanding -mgeneral-regs-only`) has no
  undefined symbol, and none of its 13 generated functions contains an
  indirect branch (GCC 13).

### Remaining

The booted `device-service` image still runs `wifi_resume` of `wifi-exec.h`;
switching it to `wifi_gen_resume` is the next step (issue #494): add
`LeanOS/Wifi/Exec.lean` to the image's generated C (`build-image.sh`,
`generate-image-object-graph.py`), include `wifi-gen-exec.h` in the
device-service kernel and call `wifi_gen_resume`, review the new syscall
call-graph rows of the entry-stack gate in both compiler lanes, and record
the `device-service`, `keyboard-echo` and `console-server` evidence. Until
then the booted executor's agreement with `Sim` remains tested, as above.
