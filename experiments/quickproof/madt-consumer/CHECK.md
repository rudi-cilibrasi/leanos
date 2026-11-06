# madt_consumer: harness check

By `tools/qp check` on 2026-11-06 19:40: upstream 56d8aa9fc5fb, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `consumer_obligations` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `consumer_obligations` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

330 mutation sites in the code under test; 328 mutants run (2 skipped as dead code, 0 not compiling).
Killed by some harness: **323/328**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `consumer_obligations` | 323/328 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `include/qotom_bsp_consumer.h:54` in `qotom_bind_validated_madt_entries`: `uint64_t result[16] = {0};` with `17`
- `include/qotom_bsp_consumer.h:98` in `qotom_bind_validated_madt_entries`: `uint64_t bound[6];` with `7`
- `include/qotom_bsp_consumer.h:72` in `qotom_bind_validated_madt_entries`: `uint64_t nmi[4] = {0,0,0,0}, nmi_count = 0;` with `5`
- `include/qotom_bsp_consumer.h:53` in `qotom_bind_validated_madt_entries`: `uint64_t state[12] = {44,0,0,0,0,0,0,256,0,0,0,0};` with `13`
- `include/qotom_bsp_consumer.h:54` in `qotom_bind_validated_madt_entries`: `uint64_t result[16] = {0};` with `1`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
