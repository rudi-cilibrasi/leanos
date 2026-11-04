# boot_text_console: harness check

By `tools/qp check` on 2026-11-04 01:51: upstream ee64a79d113c, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `boot_text_console_safe` | upstream | ok (3000 runs) |
| `boot_text_parse_complete` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `boot_text_console_safe` | ok (20 runs, no stop) |
| `boot_text_parse_complete` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

167 mutation sites in the code under test; 40 mutants run (0 skipped as dead code, 0 not compiling).
Killed by some harness: **26/40**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `boot_text_console_safe` | 19/40 |
| `boot_text_parse_complete` | 8/40 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `include/boot_text_console.h:91` in `boot_text_line`: `for (uint32_t x = 0; x < c->width; ++x)` with `1`
- `include/boot_text_console.h:31` in `boot_text_parse`: `cleared->bits = 0;` with `1`
- `include/boot_text_console.h:32` in `boot_text_parse`: `if (available < 16) return 0;` with `15`
- `include/boot_text_console.h:32` in `boot_text_parse`: `if (available < 16) return 0;` with `<=`
- `include/boot_text_console.h:99` in `boot_text_putc`: `c->busy = 1;` with `2`
- `include/boot_text_console.h:34` in `boot_text_parse`: `if (total < 16 || total > available || total > 65536 || (total & 7) ||` with `17`
- `patch/lean_export_model.c:29` in `leanos_boot_text_surface`: `if (!(pitch <= 512u)) return 0;` with `<`
- `include/boot_text_console.h:41` in `boot_text_parse`: `if (size < 8 || size > total - offset) return 0;` with `&&`
- `include/boot_text_console.h:45` in `boot_text_parse`: `if (size != 8 || offset + advance != total || !seen) return 0;` with `&&`
- `patch/lean_export_model.c:27` in `leanos_boot_text_surface`: `if (pitch % 2u != 0u) return 0;` with `==`
- `include/boot_text_console.h:34` in `boot_text_parse`: `if (total < 16 || total > available || total > 65536 || (total & 7) ||` with `<=`
- `include/boot_text_console.h:45` in `boot_text_parse`: `if (size != 8 || offset + advance != total || !seen) return 0;` with `&&`
- `include/boot_text_console.h:34` in `boot_text_parse`: `if (total < 16 || total > available || total > 65536 || (total & 7) ||` with `6`
- `include/boot_text_console.h:73` in `boot_text_enable`: `g->pitch, g->width, g->height) != 1) return 0;` with `1`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
