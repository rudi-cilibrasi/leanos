#!/usr/bin/env bash
set -euo pipefail

elf="${1:?usage: check-frame-budget-machine.sh ELF}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

symbols="$(mktemp)"
dump="$(mktemp)"
kernel_dump="$(mktemp)"
trap 'rm -f "$symbols" "$dump" "$kernel_dump"' EXIT
nm "$elf" > "$symbols"

grep -F ' leanos_frame_budget_mapping_page' "$symbols" >/dev/null || {
  echo "error: frame-budget ELF lacks generated mapping-page policy" >&2
  exit 1
}
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

objdump -d -j .user_a_text -j .user_b_text "$elf" > "$dump"
objdump -d "$elf" > "$kernel_dump"

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
