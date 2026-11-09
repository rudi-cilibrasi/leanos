# pci_capabilities: harness check

By `tools/qp check` on 2026-11-06 13:05: upstream fba97e16470d, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `capabilities_adversarial` | upstream | ok (3000 runs) |
| `capabilities_complete` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `capabilities_adversarial` | ok (20 runs, no stop) |
| `capabilities_complete` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

71 mutation sites in the code under test; 40 mutants run (0 skipped as dead code, 0 not compiling).
Killed by some harness: **36/40**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `capabilities_adversarial` | 36/40 |
| `capabilities_complete` | 23/40 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `boot/pci-capabilities.h:50` in `pci_collect_capabilities`: `const uint8_t offsets[4]={0,4,12,52};` with `5`
- `boot/pci-capabilities.h:66` in `pci_collect_capabilities`: `const uint64_t bit=UINT64_C(1)<<((offset-64)/4);` with `63`
- `boot/pci-capabilities.h:66` in `pci_collect_capabilities`: `const uint64_t bit=UINT64_C(1)<<((offset-64)/4);` with `2`
- `boot/pci-capabilities.h:66` in `pci_collect_capabilities`: `const uint64_t bit=UINT64_C(1)<<((offset-64)/4);` with `3`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
