# madt_generated_admission: harness check

By `tools/qp check` on 2026-11-07 01:49: upstream 2072292e21e3, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `admission_exact` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `admission_exact` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

209 mutation sites in the code under test; 206 mutants run (3 skipped as dead code, 0 not compiling).
Killed by some harness: **202/206**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `admission_exact` | 202/206 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `include/madt_generated_admission.h:136` in `madt_generated_entries`: `if (state[7] > 255u || state[7] != executing_apic_id)` with `6`
- `include/madt_generated_admission.h:110` in `madt_generated_entries`: `uint64_t state[12] = {44, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0};` with `13`
- `include/madt_generated_admission.h:71` in `madt_generated_envelope`: `uint64_t answer[7];` with `8`
- `include/madt_generated_admission.h:191` in `madt_generated_admission`: `uint32_t admitted_apic_id = 0;` with `1`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
