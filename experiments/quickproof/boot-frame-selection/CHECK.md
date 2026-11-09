# boot_frame_selection: harness check

By `tools/qp check` on 2026-11-07 10:00: upstream d1c5887841ce, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `frame_selection_exact` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `frame_selection_exact` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

195 mutation sites in the code under test; 191 mutants run (4 skipped as dead code, 0 not compiling).
Killed by some harness: **191/191**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `frame_selection_exact` | 191/191 |

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
