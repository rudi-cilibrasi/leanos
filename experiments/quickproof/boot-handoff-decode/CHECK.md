# boot_handoff_decode: harness check

By `tools/qp check` on 2026-11-07 07:48: upstream 7dc9113139ae, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `handoff_decode_exact` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `handoff_decode_exact` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

431 mutation sites in the code under test; 417 mutants run (14 skipped as dead code, 0 not compiling).
Killed by some harness: **410/417**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `handoff_decode_exact` | 410/417 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `include/boot_handoff_decode.h:404` in `boot_handoff_project`: `uint32_t length = 0;` with `1`
- `include/boot_handoff_decode.h:409` in `boot_handoff_project`: `uint32_t decoded = 0;` with `1`
- `include/boot_handoff_decode.h:224` in `boot_handoff_stream_copy`: `state[0], state[1], state[2], state[3], state[4], state[5],` with `2`
- `include/boot_handoff_decode.h:218` in `boot_handoff_stream_copy`: `uint64_t answer[9];` with `10`
- `include/boot_handoff_decode.h:224` in `boot_handoff_stream_copy`: `state[0], state[1], state[2], state[3], state[4], state[5],` with `1`
- `include/boot_handoff_decode.h:240` in `boot_handoff_stream_copy`: `if (state[5] != total) return BOOT_HANDOFF_STREAM_INCOMPLETE_OFFSET;` with `4`
- `include/boot_handoff_decode.h:236` in `boot_handoff_stream_copy`: `for (uint64_t word = 0; word < 7; ++word)` with `1`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
