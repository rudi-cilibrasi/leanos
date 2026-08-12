#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source_file="${LEANOS_KERNEL_SOURCE:-$repo_root/boot/kernel.c}"
elf="${1:-$repo_root/build/boot/leanos.elf}"

fail() {
  echo "error: VT-d MMIO policy: $*" >&2
  exit 1
}

[[ -f "$source_file" ]] || fail "missing kernel source: $source_file"
[[ -f "$elf" ]] || fail "missing final ELF: $elf"

# The remapping unit's window pointer is derived in exactly the four reviewed
# accessors; the only other references are the extern declaration and the
# live-mutation fixture's page computation, which never dereference the
# window.  The total is pinned so any new naming of the symbol is a policy
# error, not just new accessor-shaped derivations.
[[ "$(grep -Fc '(__vtd_mmio_window_start + offset)' "$source_file")" -eq 4 &&
   "$(grep -Fc '__vtd_mmio_window_start' "$source_file")" -eq 6 ]] ||
  fail "MMIO window derivation is not confined to the reviewed accessors"
for accessor in vtd_mmio_read32 vtd_mmio_read64 vtd_mmio_write32 \
    vtd_mmio_write64; do
  grep -Eq \
    "static __attribute__\(\(noinline, noipa\)\) (uint32_t|uint64_t|void) ${accessor}\(" \
    "$source_file" ||
    fail "reviewed accessor is missing or unpinned: $accessor"
done

# The only write sites program the global command, root pointer, context
# cache, and IOTLB registers; the sole extra write site is the controlled
# mode-26 machine negative.
[[ "$(grep -Fc 'vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND' "$source_file")" -eq 3 ]] ||
  fail "global-command write sites drifted"
[[ "$(grep -Fc 'vtd_mmio_write64(' "$source_file")" -eq 4 ]] ||
  fail "64-bit MMIO write sites drifted"
mode26_block="$(sed -n \
  '/^#if LEANOS_RETURN_CORRUPTION_MODE == 26$/,/^#endif$/p' "$source_file" |
  sed -n '/inject_vtd_translation_disable(void) {/,/^}/p')"
grep -Fq 'vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, 0);' <<<"$mode26_block" ||
  fail "translation-disable negative is not confined to the mode-26 fixture"

remap_source="$(sed -n \
  '/static __attribute__((noinline)) void vtd_boot_remap(void) {/,/^}/p' \
  "$source_file")"
[[ -n "$remap_source" ]] || fail "could not isolate the activation sequence"

line_of() {
  local text="$1" pattern="$2"
  grep -n -m1 -F "$pattern" <<<"$text" | cut -d: -f1
}

order=(
  'vtd_journal_record(1);'
  'root[word] = 0;'
  'vtd_journal_record(2);'
  'root[word] = leanos_vtd_root_table[word];'
  'vtd_journal_record(3);'
  'vtd_mmio_write64(VTD_REG_ROOT_TABLE_ADDRESS, LEANOS_VTD_ROOT_TABLE_ADDRESS);'
  'vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_SET_ROOT_TABLE);'
  'vtd_journal_record(4);'
  'vtd_mmio_write64(VTD_REG_CONTEXT_COMMAND,'
  'vtd_journal_record(5);'
  'vtd_mmio_write64(iotlb, VTD_IOTLB_INVALIDATE | VTD_IOTLB_GLOBAL);'
  'vtd_journal_record(6);'
  'vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_TRANSLATION_ENABLE);'
  'vtd_journal_record(7);'
  'fail("vtd-enabled-status");'
  'vtd_journal_record(8);'
  'leanos_validate_vtd_activation(LEANOS_VTD_PLAN_VERSION,'
)
previous_line=0
for step in "${order[@]}"; do
  step_line="$(line_of "$remap_source" "$step")"
  [[ -n "$step_line" && "$step_line" -gt "$previous_line" ]] ||
    fail "source activation order drifted at: $step"
  previous_line="$step_line"
done

# The enabled state is re-observed at the sole outbound gate.
[[ "$(grep -Fc 'verify_vtd_state();' "$source_file")" -eq 1 ]] ||
  fail "outbound re-verification is not exactly one gate call"
verify_source="$(sed -n \
  '/static __attribute__((noinline, noipa)) void verify_vtd_state(void) {/,/^}/p' \
  "$source_file")"
grep -Fq 'LEANOS_VTD_ENABLED_GSTS' <<<"$verify_source" &&
  grep -Fq 'VTD_REG_FAULT_STATUS' <<<"$verify_source" &&
  grep -Fq 'LEANOS_VTD_ROOT_TABLE_ADDRESS' <<<"$verify_source" &&
  grep -Fq 'vtd_root_table[word] != leanos_vtd_root_table[word]' \
    <<<"$verify_source" ||
  fail "outbound re-verification does not observe the complete enabled state"

symbols="$(nm "$elf")"
for symbol in vtd_boot_remap verify_vtd_state vtd_mmio_read32 vtd_mmio_read64 \
    vtd_mmio_write32 vtd_mmio_write64 vtd_journal; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" ||
    fail "final-ELF symbol missing: $symbol"
done

# Every final-ELF MMIO write call site lives in the activation sequence or the
# controlled mode-26 fixture; nothing else programs the unit.
writer_callers="$(objdump -d --no-show-raw-insn "$elf" | awk '
  /^[[:xdigit:]]+ <[^>]+>:$/ { current = $2 }
  /call.*<vtd_mmio_write(32|64)>/ { print current }
' | sort -u)"
allowed_callers='<inject_vtd_translation_disable>:
<vtd_boot_remap>:'
while IFS= read -r caller; do
  [[ -z "$caller" ]] && continue
  grep -Fxq "$caller" <<<"$allowed_callers" ||
    fail "unreviewed final-ELF MMIO write caller: $caller"
done <<<"$writer_callers"
grep -Fxq '<vtd_boot_remap>:' <<<"$writer_callers" ||
  fail "final-ELF activation sequence has no MMIO write calls"

remap_elf="$(objdump -d --no-show-raw-insn --disassemble=vtd_boot_remap "$elf")"
write_sequence="$(grep -Eo 'call.*<vtd_mmio_write(32|64)>' <<<"$remap_elf" |
  grep -Eo 'vtd_mmio_write(32|64)' | paste -sd, -)"
[[ "$write_sequence" == \
   'vtd_mmio_write64,vtd_mmio_write32,vtd_mmio_write64,vtd_mmio_write64,vtd_mmio_write32' ]] ||
  fail "final-ELF write order drifted: $write_sequence"

elf_line() {
  local text="$1" pattern="$2"
  grep -n -m1 -E "$pattern" <<<"$text" | cut -d: -f1
}
elf_last_write="$(grep -n -E 'call.*<vtd_mmio_write(32|64)>' <<<"$remap_elf" |
  tail -1 | cut -d: -f1)"
elf_generated="$(elf_line "$remap_elf" 'call.*<leanos_validate_vtd_activation>')"
[[ -n "$elf_generated" && "$elf_last_write" -lt "$elf_generated" ]] ||
  fail "final-ELF generated validation does not follow the last MMIO write"

echo "VT-d MMIO source/final-ELF policy passed"
