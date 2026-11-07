# acpi_table_copy: harness check

By `tools/qp check` on 2026-11-07 05:39: upstream 5557cd3bc232, quickproof fab76ef.

## Native runs (ASan/UBSan, 3000 runs per harness)

A failure on the unmodified code is a candidate finding; on the patched code only, a patch problem.

| harness | code | result |
|---|---|---|
| `table_copy_exact` | upstream | ok (3000 runs) |

## CompCert interpreter (20 runs per harness)

A stop is undefined behaviour in the semantics of the theorem: a finding or an idiom to patch.

| harness | result |
|---|---|
| `table_copy_exact` | ok (20 runs, no stop) |

## Mutants (300 runs per harness and mutant)

221 mutation sites in the code under test; 218 mutants run (3 skipped as dead code, 0 not compiling).
Killed by some harness: **205/218**; 0 of the others only hang (the laws do not claim termination).

| harness | killed |
|---|---|
| `table_copy_exact` | 205/218 |

Survivors (an equivalent mutant, behaviour no law checks, or a failure the native runs did not reach):

- `include/acpi_table_copy.h:150` in `acpi_copy_sdt`: `for (uint32_t byte = 0; byte < chunk_bytes; ++byte)` with `1`
- `include/acpi_table_copy.h:227` in `acpi_decode_root_entry`: `if (index >= entries->count ||` with `&&`
- `include/acpi_table_copy.h:348` in `acpi_copy_root_and_tables`: `selected_root->bytes != storage->root || selected_root->length < 36u)` with `&&`
- `include/acpi_table_copy.h:168` in `acpi_validate_copied_sdt`: `if (table->bytes == 0 || table->length < 36u ||` with `&&`
- `include/acpi_table_copy.h:357` in `acpi_copy_root_and_tables`: `if (root_entries->bytes != selected_root->bytes + 36u ||` with `&&`
- `include/acpi_table_copy.h:370` in `acpi_copy_root_and_tables`: `const struct copied_acpi_sdt *selected_madt = 0;` with `1`
- `include/acpi_table_copy.h:283` in `acpi_copy_root_tables`: `if (copied->physical_address != addresses[entry] ||` with `&&`
- `include/acpi_table_copy.h:110` in `acpi_copy_sdt`: `(uint32_t)header[7] << 24;` with `23`
- `include/acpi_table_copy.h:168` in `acpi_validate_copied_sdt`: `if (table->bytes == 0 || table->length < 36u ||` with `1`
- `include/acpi_table_copy.h:227` in `acpi_decode_root_entry`: `if (index >= entries->count ||` with `>`
- `include/acpi_table_copy.h:172` in `acpi_validate_copied_sdt`: `(uint32_t)table->bytes[7] << 24) != table->length ||` with `23`
- `include/acpi_table_copy.h:347` in `acpi_copy_root_and_tables`: `if (selected_root->physical_address != selected_address ||` with `&&`
- `include/acpi_table_copy.h:363` in `acpi_copy_root_and_tables`: `uint32_t copied_table_count = 0;` with `1`

## VST lint

Constructs that are defined C but that VST cannot prove (switches falling off their end, composites with
bitfield members in the generated Clight; and in the Clight of each law's cone, tools/clight_audit.py: switches on a
non-int, goto, struct copies, parameters and results, builtins, externals outside the environment, byte copies of
pointer-holding memory) (fix in the harness, or by an idiom patch in the code under test):

clean
