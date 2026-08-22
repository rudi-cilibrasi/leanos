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

# The boot-remap write sites program the global command, root pointer, context
# cache, and IOTLB registers.  The other reviewed sites are the controlled
# mode-26 machine negative and the assigned-EDU scenario's four
# write-one-to-clear operations after each exact fault binding succeeds.
[[ "$(grep -Fc 'vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND' "$source_file")" -eq 3 ]] ||
  fail "global-command write sites drifted"
[[ "$(grep -Fc 'vtd_mmio_write64(' "$source_file")" -eq 8 ]] ||
  fail "64-bit MMIO write sites drifted"
mode26_block="$(sed -n \
  '/^#if LEANOS_RETURN_CORRUPTION_MODE == 26$/,/^#endif$/p' "$source_file" |
  sed -n '/inject_vtd_translation_disable(void) {/,/^}/p')"
grep -Fq 'vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, 0);' <<<"$mode26_block" ||
  fail "translation-disable negative is not confined to the mode-26 fixture"

line_of() {
  local text="$1" pattern="$2"
  grep -n -m1 -F "$pattern" <<<"$text" | cut -d: -f1 || true
}

assigned_transfer_block="$(sed -n '/static __attribute__((noinline)) void run_assigned_edu_transfers(void) {/,/^}/p' "$source_file")"
grep -Fq 'leanos_validate_assigned_edu_fault(' <<<"$assigned_transfer_block" &&
  grep -Fq 'vtd_invalidate_global_iotlb();' <<<"$assigned_transfer_block" &&
  grep -Fq 'vtd_mmio_write64(0x228, UINT64_C(1) << 63);' <<<"$assigned_transfer_block" &&
  grep -Fq 'fail("vtd-assigned-fault-clear");' <<<"$assigned_transfer_block" &&
  grep -Fq 'fail("vtd-assigned-write-fault-clear");' <<<"$assigned_transfer_block" &&
  grep -Fq 'fail("vtd-assigned-unmapped-fault-clear");' <<<"$assigned_transfer_block" ||
  fail "assigned-EDU fault probe/clear is not bound to the reviewed scenario"

# Frame reuse has a stricter order than the earlier fault probes: remove the
# old leaf, complete invalidation, acknowledge the generated publication,
# scrub and republish at the fresh IOVA, prove the old IOVA faults, and only
# then restore the canonical boot mapping.  Pin all three invalidation calls
# inside that bounded source block so an incidental reset or earlier flush
# cannot satisfy the evidence policy.
assigned_reuse_block="$(sed -n \
  '/\/\* Exercise the hardware half of frame reuse/,/reset=0 result=PASS\\n");/p' \
  "$source_file")"
[[ -n "$assigned_reuse_block" ]] ||
  fail "could not isolate the assigned-EDU frame-reuse sequence"
mapfile -t reuse_invalidation_lines < <(
  grep -n -F 'vtd_invalidate_global_iotlb();' <<<"$assigned_reuse_block" |
    cut -d: -f1
)
[[ "${#reuse_invalidation_lines[@]}" -eq 3 ]] ||
  fail "assigned-EDU frame reuse does not contain exactly three invalidations"
reuse_prepare="$(line_of "$assigned_reuse_block" \
  'leanos_assigned_edu_reuse_publication(')"
reuse_unpublish="$(line_of "$assigned_reuse_block" \
  '((volatile uint64_t *)vtd_second_level_table)[0] = 0;')"
reuse_complete="$(line_of "$assigned_reuse_block" \
  '2, 1, LEANOS_VTD_ASSIGNED_REQUESTER')"
reuse_scrub="$(line_of "$assigned_reuse_block" \
  'for (uint64_t word = 0; word < PAGE_BYTES / sizeof(uint64_t); ++word)')"
reuse_republish="$(line_of "$assigned_reuse_block" \
  '((volatile uint64_t *)vtd_second_level_table)[2] =')"
reuse_old_denial="$(line_of "$assigned_reuse_block" \
  'fail("vtd-reuse-old-iova-access");')"
reuse_fresh_transfer="$(line_of "$assigned_reuse_block" \
  'fail("vtd-reuse-fresh-iova-transfer");')"
reuse_restore="$(line_of "$assigned_reuse_block" \
  'leanos_vtd_assigned_second_level_table[0];')"
[[ -n "$reuse_prepare" && -n "$reuse_unpublish" &&
   -n "$reuse_complete" && -n "$reuse_scrub" &&
   -n "$reuse_republish" && -n "$reuse_old_denial" &&
   -n "$reuse_fresh_transfer" && -n "$reuse_restore" ]] ||
  fail "assigned-EDU frame-reuse source order drifted"
[[ "$reuse_prepare" -lt "$reuse_unpublish" &&
   "$reuse_unpublish" -lt "${reuse_invalidation_lines[0]}" &&
   "${reuse_invalidation_lines[0]}" -lt "$reuse_complete" &&
   "$reuse_complete" -lt "$reuse_scrub" &&
   "$reuse_scrub" -lt "$reuse_republish" &&
   "$reuse_republish" -lt "${reuse_invalidation_lines[1]}" &&
   "${reuse_invalidation_lines[1]}" -lt "$reuse_old_denial" &&
   "$reuse_old_denial" -lt "$reuse_fresh_transfer" &&
   "$reuse_fresh_transfer" -lt "$reuse_restore" &&
   "$reuse_restore" -lt "${reuse_invalidation_lines[2]}" ]] ||
  fail "assigned-EDU frame-reuse source order drifted"
iotlb_source="$(sed -n '/static __attribute__((noinline)) void vtd_invalidate_global_iotlb(void) {/,/^}/p' "$source_file")"
grep -Fq 'vtd_mmio_read64(VTD_REG_EXTENDED_CAPABILITY);' <<<"$iotlb_source" &&
  grep -Fq 'extended_capability != LEANOS_VTD_EXPECTED_ECAP' <<<"$iotlb_source" &&
  grep -Fq 'vtd_mmio_write64(iotlb, VTD_IOTLB_INVALIDATE | VTD_IOTLB_GLOBAL);' <<<"$iotlb_source" &&
  grep -Fq 'vtd_wait_invalidation(iotlb, VTD_IOTLB_INVALIDATE);' <<<"$iotlb_source" ||
  fail "shared bounded global-IOTLB invalidation drifted"

remap_source="$(sed -n \
  '/static __attribute__((noinline)) void vtd_boot_remap(void) {/,/^}/p' \
  "$source_file")"
[[ -n "$remap_source" ]] || fail "could not isolate the activation sequence"

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
  'vtd_invalidate_global_iotlb();'
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
<run_assigned_edu_transfers>:
<vtd_boot_remap>:
<vtd_invalidate_global_iotlb>:'
while IFS= read -r caller; do
  [[ -z "$caller" ]] && continue
  grep -Fxq "$caller" <<<"$allowed_callers" ||
    fail "unreviewed final-ELF MMIO write caller: $caller"
done <<<"$writer_callers"
grep -Fxq '<vtd_boot_remap>:' <<<"$writer_callers" ||
  fail "final-ELF activation sequence has no MMIO write calls"
grep -Fxq '<vtd_invalidate_global_iotlb>:' <<<"$writer_callers" ||
  fail "final-ELF global-IOTLB helper has no MMIO write call"

if grep -Eq '[[:space:]]run_assigned_edu_transfers$' <<<"$symbols"; then
  grep -Fxq '<run_assigned_edu_transfers>:' <<<"$writer_callers" ||
    fail "assigned-EDU final ELF omits the reviewed fault clear"
  assigned_transfer_elf="$(objdump -d --no-show-raw-insn --disassemble=run_assigned_edu_transfers "$elf")"
  assigned_write_sequence="$(
    grep -Eo 'call.*<vtd_mmio_write(32|64)>' <<<"$assigned_transfer_elf" |
      grep -Eo 'vtd_mmio_write(32|64)' | paste -sd, -
  )"
  [[ "$assigned_write_sequence" == \
     'vtd_mmio_write64,vtd_mmio_write64,vtd_mmio_write64,vtd_mmio_write64' ]] ||
    fail "assigned-EDU final-ELF fault-clear sequence drifted: $assigned_write_sequence"

  mapfile -t assigned_iotlb_calls < <(
    grep -n -E 'call.*<vtd_invalidate_global_iotlb>' \
      <<<"$assigned_transfer_elf" | cut -d: -f1
  )
  mapfile -t assigned_model_calls < <(
    grep -n -E 'call.*<leanos_assigned_edu_reuse_publication>' \
      <<<"$assigned_transfer_elf" | cut -d: -f1
  )
  [[ "${#assigned_model_calls[@]}" -eq 2 ]] ||
    fail "assigned-EDU final ELF does not contain both generated reuse calls"
  if [[ "${LEANOS_EXPECT_OMIT_REUSE_INVALIDATION:-0}" == 1 ]]; then
    [[ "${#assigned_iotlb_calls[@]}" -eq 4 &&
       "${assigned_model_calls[0]}" -lt "${assigned_model_calls[1]}" &&
       "${assigned_model_calls[1]}" -lt "${assigned_iotlb_calls[3]}" ]] ||
      fail "assigned-EDU omitted-invalidation fixture order drifted"
  else
    [[ "${#assigned_iotlb_calls[@]}" -eq 6 ]] ||
      fail "assigned-EDU final ELF does not contain the six reviewed IOTLB calls"
    [[ "${assigned_model_calls[0]}" -lt "${assigned_iotlb_calls[3]}" &&
       "${assigned_iotlb_calls[3]}" -lt "${assigned_model_calls[1]}" &&
       "${assigned_model_calls[1]}" -lt "${assigned_iotlb_calls[4]}" &&
       "${assigned_iotlb_calls[4]}" -lt "${assigned_iotlb_calls[5]}" ]] ||
      fail "assigned-EDU final-ELF frame-reuse order drifted"
  fi
fi

remap_elf="$(objdump -d --no-show-raw-insn --disassemble=vtd_boot_remap "$elf")"
write_sequence="$(grep -Eo 'call.*<vtd_mmio_write(32|64)>' <<<"$remap_elf" |
  grep -Eo 'vtd_mmio_write(32|64)' | paste -sd, -)"
[[ "$write_sequence" == \
   'vtd_mmio_write64,vtd_mmio_write32,vtd_mmio_write64,vtd_mmio_write32' ]] ||
  fail "final-ELF write order drifted: $write_sequence"
grep -Eq 'call.*<vtd_invalidate_global_iotlb>' <<<"$remap_elf" ||
  fail "final-ELF activation sequence omits global-IOTLB invalidation"

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
