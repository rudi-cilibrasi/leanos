#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source_file="${LEANOS_KERNEL_SOURCE:-$repo_root/boot/kernel.c}"
elf="${1:-$repo_root/build/boot/leanos.elf}"

fail() {
  echo "error: runtime invalidation policy: $*" >&2
  exit 1
}

[[ -f "$source_file" ]] || fail "missing kernel source: $source_file"
[[ -f "$elf" ]] || fail "missing final ELF: $elf"

grep -Fqx '#define RUNTIME_MAPPING_PAGE 7u' "$source_file" ||
  fail "mutable-window target is not confined to page 7"
relation_source="$(
  sed -n '/^static .*checked_runtime_leaf(/,/^}/p' "$source_file"
)"
[[ -n "$relation_source" ]] ||
  fail "mutable-leaf relation is missing"
for state in BOOT BEFORE UNMAPPED AFTER REUSED; do
  grep -Fq "#define RUNTIME_MAPPING_STATE_${state} " "$source_file" ||
    fail "mutable-window state relation is incomplete: $state"
  grep -Fq "case RUNTIME_MAPPING_STATE_${state}:" <<<"$relation_source" ||
    fail "mutable-leaf relation does not handle state: $state"
done
grep -Fq 'if (page != RUNTIME_MAPPING_PAGE || (space != 1 && space != 2))' \
  <<<"$relation_source" ||
  fail "mutable-leaf exception is not confined to address spaces A/B page 7"
grep -Fq 'if (space == 1)' <<<"$relation_source" &&
  grep -Fq '*expected = runtime_mapping_leaf(runtime_mapping_frame_before);' \
    <<<"$relation_source" ||
  fail "fresh-owner relation does not bind A/page 7 to the reused frame"
grep -Fq 'default:' <<<"$relation_source" &&
  grep -Fq 'return 0;' <<<"$relation_source" ||
  fail "unknown mutable-leaf states are not rejected"
relation_checks=(
  runtime-invlpg-relation
  runtime-cr3-relation
  runtime-invlpg-before-relation
  runtime-invlpg-after-relation
  runtime-cr3-before-relation
  runtime-cr3-after-relation
  runtime-window-restore-relation
  stale-translation-arm-relation
  runtime-reuse-relation
  stale-translation-new-owner-relation
)
[[ "$(grep -Fc 'require_runtime_mapping_relation("' "$source_file")" -eq \
    "${#relation_checks[@]}" ]] ||
  fail "mutable-leaf relation is not checked at every phase"
for relation_check in "${relation_checks[@]}"; do
  [[ "$(grep -Fc \
      "require_runtime_mapping_relation(\"${relation_check}\");" \
      "$source_file")" -eq 1 ]] ||
    fail "mutable-leaf relation is not checked at every phase"
done
grep -Fq 'LEANOS_COMPOSITE_STATE_DIRECT_MAPPED,' "$source_file" ||
  fail "canonical pre-state authority is missing"
grep -Fq 'LEANOS_COMPOSITE_COMMAND_ACCEPTED_SYSCALL_UNMAP,' "$source_file" ||
  fail "canonical unmap command is missing"
grep -Fq 'RUNTIME_MAPPING_PAGE, 0, 0, 0);' "$source_file" ||
  fail "canonical page-7 argument or zero reserved arguments drifted"
[[ "$(grep -Fc \
  'canonical_reply != LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED' \
  "$source_file")" -eq 4 ]] ||
  fail "closed typed-reply checks drifted"
[[ "$(grep -Fc \
  '((volatile uint64_t *)page_table_b)[RUNTIME_MAPPING_PAGE] = 0;' \
  "$source_file")" -eq 2 ]] ||
  fail "PTE mutation is not confined to address space B/page 7"
[[ "$(grep -Fc 'runtime_invlpg_publication = canonical_reply;' \
  "$source_file")" -eq 1 ]] ||
  fail "INVLPG completion publication drifted"
[[ "$(grep -Fc 'runtime_cr3_publication = canonical_reply;' \
  "$source_file")" -eq 1 ]] ||
  fail "CR3 completion publication drifted"

source_function() {
  local name="$1"
  sed -n "/static void ${name}(/,/^}/p" "$source_file"
}

invlpg_source="$(source_function runtime_unmap_page7_invlpg)"
cr3_source="$(source_function runtime_unmap_page7_cr3)"
reuse_source="$(source_function runtime_reuse_page7_frame)"
[[ -n "$invlpg_source" && -n "$cr3_source" && -n "$reuse_source" ]] ||
  fail "could not isolate machine helpers"
[[ "$(grep -Fc 'invlpg (%0)' <<<"$invlpg_source")" -eq 1 ]] ||
  fail "active-root path does not contain exactly one INVLPG"
[[ "$(grep -Fc '"r"((uint64_t)page_map_level_4_b)' <<<"$cr3_source")" -eq 1 ]] ||
  fail "inactive-root path does not select exactly address space B"

line_of() {
  local text="$1" pattern="$2"
  grep -n -m1 -F "$pattern" <<<"$text" | cut -d: -f1
}

source_invlpg_store="$(line_of "$invlpg_source" \
  '((volatile uint64_t *)page_table_b)[RUNTIME_MAPPING_PAGE] = 0;')"
source_invlpg_instruction="$(line_of "$invlpg_source" 'invlpg (%0)')"
source_invlpg_publish="$(line_of "$invlpg_source" \
  'runtime_invlpg_publication = canonical_reply;')"
[[ "$source_invlpg_store" -lt "$source_invlpg_instruction" &&
   "$source_invlpg_instruction" -lt "$source_invlpg_publish" ]] ||
  fail "source INVLPG order is not PTE-store, invalidate, publish"

source_cr3_store="$(line_of "$cr3_source" \
  '((volatile uint64_t *)page_table_b)[RUNTIME_MAPPING_PAGE] = 0;')"
source_cr3_instruction="$(line_of "$cr3_source" 'mov %0, %%cr3')"
source_cr3_publish="$(line_of "$cr3_source" \
  'runtime_cr3_publication = canonical_reply;')"
[[ "$source_cr3_store" -lt "$source_cr3_instruction" &&
   "$source_cr3_instruction" -lt "$source_cr3_publish" ]] ||
  fail "source CR3 order is not PTE-store, root-load, publish"

grep -Fq \
  'leanos_stale_translation_demo(0, 0, 1, RUNTIME_MAPPING_PAGE, 0, 1);' \
  <<<"$reuse_source" ||
  fail "same-frame reuse is not bound to the generated post-reuse state"
grep -Fq 'model_reply != RUNTIME_REUSE_MODEL_REPLY' <<<"$reuse_source" ||
  fail "same-frame reuse does not check the generated model reply"
grep -Fq 'runtime_invlpg_publication != canonical_reply' <<<"$reuse_source" ||
  fail "same-frame reuse is not sequenced after accepted invalidation"
grep -Fq 'page_table_b[RUNTIME_MAPPING_PAGE] != 0' <<<"$reuse_source" ||
  fail "same-frame reuse does not require the old leaf absent"
grep -Fq \
  '((volatile uint64_t *)page_table_a)[RUNTIME_MAPPING_PAGE] =' \
  <<<"$reuse_source" ||
  fail "same-frame reuse does not map the scrubbed frame to the new owner"
source_reuse_scrub="$(line_of "$reuse_source" 'frame[i] = 0;')"
source_reuse_allocate="$(line_of "$reuse_source" 'runtime_reuse_lifetime = 2;')"
source_reuse_canary="$(line_of "$reuse_source" 'frame[0] = RUNTIME_MAPPING_AFTER;')"
source_reuse_map="$(line_of "$reuse_source" \
  '((volatile uint64_t *)page_table_a)[RUNTIME_MAPPING_PAGE] =')"
source_reuse_state="$(line_of "$reuse_source" \
  'runtime_mapping_state = RUNTIME_MAPPING_STATE_REUSED;')"
source_reuse_publish="$(line_of "$reuse_source" \
  'runtime_reuse_publication = model_reply;')"
[[ "$source_reuse_scrub" -lt "$source_reuse_allocate" &&
   "$source_reuse_allocate" -lt "$source_reuse_canary" &&
   "$source_reuse_canary" -lt "$source_reuse_map" &&
   "$source_reuse_map" -lt "$source_reuse_state" &&
   "$source_reuse_state" -lt "$source_reuse_publish" ]] ||
  fail "source reuse order is not scrub, allocate, canary, map-new-owner, publish"

symbols="$(nm "$elf")"
for symbol in runtime_unmap_page7_invlpg runtime_unmap_page7_cr3 \
    runtime_invlpg_publication runtime_cr3_publication \
    runtime_mapping_frame_before runtime_mapping_frame_after; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" ||
    fail "final-ELF symbol missing: $symbol"
done
if [[ "$(basename "$elf")" == *stale-translation* ]]; then
  for symbol in runtime_reuse_page7_frame runtime_reuse_publication \
      runtime_reuse_owner runtime_reuse_lifetime; do
    grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" ||
      fail "stale-translation final-ELF symbol missing: $symbol"
  done
fi

disassemble() {
  objdump -d --no-show-raw-insn --disassemble="$1" "$elf"
}

invlpg_elf="$(disassemble runtime_unmap_page7_invlpg)"
cr3_elf="$(disassemble runtime_unmap_page7_cr3)"
page_table_b_hex="$(nm -n "$elf" | awk '$3 == "page_table_b" { print $1 }')"
[[ "$page_table_b_hex" =~ ^[[:xdigit:]]+$ ]] ||
  fail "could not resolve address space B page table"
printf -v page_table_b_page7_hex '%x' "$((16#$page_table_b_hex + 0x38))"
page_table_b_page7_ref="#[[:space:]]+${page_table_b_page7_hex}[[:space:]]"
[[ "$(grep -Ec '[[:space:]]invlpg[[:space:]]' <<<"$invlpg_elf")" -eq 1 ]] ||
  fail "final-ELF active-root path does not contain exactly one INVLPG"
grep -Eq 'mov[[:space:]]+\$0x7000,%e?[a-z0-9]+' <<<"$invlpg_elf" ||
  fail "final-ELF INVLPG operand is not confined to virtual page 7"
grep -Eq "$page_table_b_page7_ref" <<<"$invlpg_elf" ||
  fail "final-ELF INVLPG path does not mutate B/page 7"
grep -Eq '<runtime_invlpg_publication>' <<<"$invlpg_elf" ||
  fail "final-ELF INVLPG publication store missing"

[[ "$(grep -Ec 'mov[[:space:]]+%r[a-z0-9]+,%cr3' <<<"$cr3_elf")" -eq 1 ]] ||
  fail "final-ELF inactive-root path does not contain exactly one CR3 load"
grep -Eq "$page_table_b_page7_ref" <<<"$cr3_elf" ||
  fail "final-ELF CR3 path does not mutate B/page 7"
root_b_hex="$(nm -n "$elf" | awk '$3 == "page_map_level_4_b" { print $1 }')"
[[ "$root_b_hex" =~ ^[[:xdigit:]]+$ ]] ||
  fail "could not resolve address space B root"
printf -v root_b_immediate '%x' "$((16#$root_b_hex))"
grep -Eq "\\\$0x${root_b_immediate},%e?[a-z0-9]+" <<<"$cr3_elf" ||
  fail "final-ELF CR3 target is not address space B"
grep -Eq '<runtime_cr3_publication>' <<<"$cr3_elf" ||
  fail "final-ELF CR3 publication store missing"

elf_line() {
  local text="$1" pattern="$2"
  grep -n -m1 -E "$pattern" <<<"$text" | cut -d: -f1
}

elf_invlpg_store="$(elf_line "$invlpg_elf" "$page_table_b_page7_ref")"
elf_invlpg_instruction="$(elf_line "$invlpg_elf" \
  '[[:space:]]invlpg[[:space:]]')"
elf_invlpg_publish="$(elf_line "$invlpg_elf" \
  '<runtime_invlpg_publication>')"
[[ "$elf_invlpg_store" -lt "$elf_invlpg_instruction" &&
   "$elf_invlpg_instruction" -lt "$elf_invlpg_publish" ]] ||
  fail "final-ELF INVLPG order is not PTE-store, invalidate, publish"

elf_cr3_store="$(elf_line "$cr3_elf" "$page_table_b_page7_ref")"
elf_cr3_instruction="$(elf_line "$cr3_elf" \
  'mov[[:space:]]+%r[a-z0-9]+,%cr3')"
elf_cr3_publish="$(elf_line "$cr3_elf" '<runtime_cr3_publication>')"
[[ "$elf_cr3_store" -lt "$elf_cr3_instruction" &&
   "$elf_cr3_instruction" -lt "$elf_cr3_publish" ]] ||
  fail "final-ELF CR3 order is not PTE-store, root-load, publish"

echo "Runtime mapping invalidation source/final-ELF policy passed"
