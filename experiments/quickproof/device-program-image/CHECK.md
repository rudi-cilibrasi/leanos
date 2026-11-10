# device_program_image: harness check

By `tools/qp check` on 2026-11-09 20:50: upstream 8f328b08e382, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `image_exact` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `image_exact` | ok (20 runs, no stop) |

## Mutants (1000 runs per harness and mutant)

282 mutation sites in the code under test; 259 mutants run (21 skipped as dead code, 2 not compiling).
Killed by some harness: **255/259**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `image_exact` | 255/259 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `hardware/wifi/wifi-exec.h:286` in `wifi_start`: `uint32_t hdr = 0;` with `1`
- `hardware/wifi/wifi-exec.h:105` in `wifi_is_sink`: `if (p->sinks[i] == off) return 1;` with `2`
- `hardware/wifi/wifi-exec.h:99` in `wifi_has_desc`: `p->descs[i].count == d->count && p->descs[i].stride == d->stride) return 1;` with `2`
- `hardware/wifi/wifi-exec.h:241` in `wifi_image_header`: `pol->sink_count = image_len >= 68 ? wifi_le32(image + 64) : 0xffffffffu;` with `67`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
