# pci_enumeration: harness check

By `tools/qp check` on 2026-11-06 16:55: upstream fba97e16470d, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `enumeration_exact` | upstream | ok (3000 runs) |

## CompCert interpreter (10 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `enumeration_exact` | ok (10 runs, no stop) |

## Mutants (300 runs per harness and mutant)

34 mutation sites in the code under test; 34 mutants run (0 skipped as dead code, 0 not compiling).
Killed by some harness: **34/34**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `enumeration_exact` | 34/34 |

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
