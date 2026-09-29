# ADR 0020: Assurance for the device-program executor

## Status

Accepted. Resolves the research question in issue #451.

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
