#!/usr/bin/env bash
set -euo pipefail

elf="${1:?usage: check-frame-budget-machine.sh ELF}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
source_file="${LEANOS_KERNEL_SOURCE:-$root/boot/kernel.c}"

symbols="$(mktemp)"
dump="$(mktemp)"
kernel_dump="$(mktemp)"
trap 'rm -f "$symbols" "$dump" "$kernel_dump"' EXIT
[[ -f "$source_file" ]] || {
  echo "error: frame-budget kernel source is missing: $source_file" >&2
  exit 1
}
nm "$elf" > "$symbols"

grep -F ' leanos_frame_budget_mapping_page' "$symbols" >/dev/null || {
  echo "error: frame-budget ELF lacks generated mapping-page policy" >&2
  exit 1
}
grep -F ' leanos_frame_budget_invalidation_effect' "$symbols" >/dev/null || {
  echo "error: frame-budget ELF lacks generated invalidation-effect policy" >&2
  exit 1
}
grep -F ' leanos_boot_projection_finish' "$symbols" >/dev/null &&
  grep -F ' leanos_boot_publish_authority' "$symbols" >/dev/null || {
  echo "error: frame-budget ELF lacks rich first-eligible publication authority" >&2
  exit 1
}
if grep -F ' leanos_boot_select_frame' "$symbols" >/dev/null; then
  echo "error: frame-budget ELF retained scalar selector authority" >&2
  exit 1
fi
if grep -F 'frame_budget_reuse_frame' "$symbols" >/dev/null; then
  echo "error: frame-budget ELF retained static-buffer substitution" >&2
  exit 1
fi
strings "$elf" | grep -F 'frame-budget-double-publication' >/dev/null || {
  echo "error: frame-budget ELF lacks the physical-frame publication guard" >&2
  exit 1
}
strings "$elf" | grep -F 'frame-budget-b-context-canary' >/dev/null || {
  echo "error: frame-budget ELF lacks the fresh-B register guard" >&2
  exit 1
}
strings "$elf" | grep -F 'frame-budget-projection-authority' >/dev/null &&
  strings "$elf" | grep -F 'frame-budget-publication-authority' >/dev/null || {
  echo "error: frame-budget ELF lacks second-frame authority checks" >&2
  exit 1
}

retire_source="$(
  sed -n '/static void frame_budget_retire_mapping(/,/^}/p' "$source_file"
)"
[[ -n "$retire_source" ]] || {
  echo "error: frame-budget retirement helper is missing" >&2
  exit 1
}
grep -Fq 'effect_token != LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN' \
  <<<"$retire_source" || {
  echo "error: frame-budget retirement lacks the generated exact-effect check" >&2
  exit 1
}
grep -Fq '(cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_b' \
  <<<"$retire_source" || {
  echo "error: frame-budget retirement is not bound to the active B root" >&2
  exit 1
}
grep -Fq '(cr4 & (UINT64_C(1) << 17)) != 0' <<<"$retire_source" || {
  echo "error: frame-budget retirement does not reject PCID" >&2
  exit 1
}
[[ "$(grep -Fc '((volatile uint64_t *)page_table)[page] = 0;' \
    <<<"$retire_source")" -eq 1 ]] || {
  echo "error: frame-budget retirement PTE store drifted" >&2
  exit 1
}
[[ "$(grep -Fc '"r"((uint64_t)page_map_level_4_b)' \
    <<<"$retire_source")" -eq 1 ]] || {
  echo "error: frame-budget retirement lacks one exact CR3 reload" >&2
  exit 1
}
line_of() {
  grep -n -m1 -F "$2" <<<"$1" | cut -d: -f1
}
source_store="$(line_of "$retire_source" \
  '((volatile uint64_t *)page_table)[page] = 0;')"
source_flush="$(line_of "$retire_source" \
  '"r"((uint64_t)page_map_level_4_b)')"
source_ack="$(line_of "$retire_source" \
  'frame_budget_retirement_completion = effect_token;')"
source_publish="$(line_of "$retire_source" \
  'frame_budget_publication_live = 0;')"
[[ "$source_store" -lt "$source_flush" &&
   "$source_flush" -lt "$source_ack" &&
   "$source_ack" -lt "$source_publish" ]] || {
  echo "error: frame-budget retirement order is not PTE-store, CR3-flush, acknowledge, publish" >&2
  exit 1
}
grep -Fq 'frame_budget_retirement_completion !=' "$source_file" &&
  grep -Fq 'fail("frame-budget-scrub-before-invalidation");' "$source_file" &&
  grep -Fq 'fail("frame-budget-publish-before-invalidation");' "$source_file" || {
  echo "error: frame-budget scrub/reuse is not guarded by invalidation completion" >&2
  exit 1
}

objdump -d -j .user_a_text -j .user_b_text "$elf" > "$dump"
objdump -d "$elf" > "$kernel_dump"

retire_elf="$(
  sed -n '/<frame_budget_retire_mapping>:/,/^$/p' "$kernel_dump"
)"
[[ -n "$retire_elf" ]] || {
  echo "error: frame-budget final ELF lacks the retirement helper" >&2
  exit 1
}
[[ "$(grep -Ec 'mov[[:space:]]+%r[a-z0-9]+,%cr3' \
    <<<"$retire_elf")" -eq 1 ]] || {
  echo "error: frame-budget final ELF lacks one retirement CR3 flush" >&2
  exit 1
}
grep -F '<frame_budget_retirement_completion>' <<<"$retire_elf" >/dev/null || {
  echo "error: frame-budget final ELF lacks invalidation acknowledgement" >&2
  exit 1
}
grep -F '<frame_budget_publication_live>' <<<"$retire_elf" >/dev/null || {
  echo "error: frame-budget final ELF lacks retirement publication" >&2
  exit 1
}
elf_line() {
  grep -n -m1 -E "$2" <<<"$1" | cut -d: -f1
}
elf_store="$(elf_line "$retire_elf" \
  'movq?[[:space:]]+\$0x0,(0x[0-9a-f]+)?\((%r[a-z0-9]+)?,%r[a-z0-9]+,8\)')"
elf_flush="$(elf_line "$retire_elf" 'mov[[:space:]]+%r[a-z0-9]+,%cr3')"
elf_ack="$(elf_line "$retire_elf" \
  'mov[[:space:]]+%r[a-z0-9]+,.*<frame_budget_retirement_completion>')"
elf_publish="$(elf_line "$retire_elf" \
  'movl?[[:space:]]+\$0x0,.*<frame_budget_publication_live>')"
[[ "$elf_store" -lt "$elf_flush" &&
   "$elf_flush" -lt "$elf_ack" &&
   "$elf_ack" -lt "$elf_publish" ]] || {
  echo "error: frame-budget final-ELF retirement order is not store, flush, acknowledge, publish" >&2
  exit 1
}

isr80="$(sed -n '/<isr80>:/,/<isr14>:/p' "$kernel_dump")"
feed_line="$(grep -n -m1 'cmp[[:space:]]\+\$0xfeed,%rax' <<< "$isr80" |
  cut -d: -f1 || true)"
[[ -n "$feed_line" ]] || {
  echo "error: frame-budget ELF lacks the subject-B dispatch result" >&2
  exit 1
}
fresh_switch="$(sed -n "${feed_line},$((feed_line + 18))p" <<< "$isr80")"
grep -F '<initial_context_b>' <<< "$fresh_switch" >/dev/null &&
  grep -Eq 'mov[[:space:]]+\$0x14,%ecx' <<< "$fresh_switch" &&
  grep -Eq 'rep movsq' <<< "$fresh_switch" &&
  grep -Eq 'mov[[:space:]]+%rax,%cr3' <<< "$fresh_switch" &&
  grep -Eq '%rax.*initial_context_b\+0x[0-9a-f]+>' <<< "$fresh_switch" || {
  echo "error: subject B is not restored from a complete kernel-owned context" >&2
  exit 1
}

user_a="$(sed -n '/Disassembly of section .user_a_text:/,/Disassembly of section .user_b_text:/p' "$dump")"
grep -Eq 'movb[[:space:]]+\$0xa5,\(%rax\)' <<< "$user_a" || {
  echo "error: subject A lacks direct CPL3 first-byte canary write" >&2
  exit 1
}
grep -Eq 'movb[[:space:]]+\$0xa5,0xfff\(%rax\)' <<< "$user_a" || {
  echo "error: subject A lacks direct CPL3 last-byte canary write" >&2
  exit 1
}

user_b="$(sed -n '/Disassembly of section .user_b_text:/,$p' "$dump")"
for canary in \
    '0x10001,%rax' '0x20002,%rbx' '0x30003,%rcx' '0x40004,%rdx' \
    '0x50005,%rbp' '0x60006,%rsi' '0x70007,%rdi' '0x80008,%r8' \
    '0x90009,%r9' '0x100010,%r10' '0x110011,%r11' \
    '0x140014,%r14' '0x150015,%r15'; do
  grep -Eq "cmp[[:space:]]+\\\$$canary" <<< "$user_b" || {
    echo "error: subject B lacks entry canary check for ${canary#*,}" >&2
    exit 1
  }
done
grep -Eq 'movabs[[:space:]]+\$0xc0dec0dec0dec0de,%rax' <<< "$user_b" &&
  grep -Eq 'cmp[[:space:]]+%rax,%r12' <<< "$user_b" &&
  grep -Eq 'movabs[[:space:]]+\$0x51a7e51a7e51a7e5,%rax' <<< "$user_b" &&
  grep -Eq 'cmp[[:space:]]+%rax,%r13' <<< "$user_b" || {
  echo "error: subject B lacks full-width entry canary checks" >&2
  exit 1
}
grep -Eq 'movabs[[:space:]]+\$0xb2b2f11251a7e55e,%rbx' <<< "$user_b" || {
  echo "error: subject B lacks the checked fresh-context attestation" >&2
  exit 1
}
grep -Eq 'movzbl[[:space:]]+\(%rax\),%ebx' <<< "$user_b" || {
  echo "error: subject B lacks direct CPL3 first-byte reuse read" >&2
  exit 1
}
grep -Eq 'movzbl[[:space:]]+0xfff\(%rax\),%ecx' <<< "$user_b" || {
  echo "error: subject B lacks direct CPL3 last-byte reuse read" >&2
  exit 1
}

echo "Frame-budget allocator binding, fresh B context, and direct CPL3 canary sites passed"
