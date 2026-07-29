#!/usr/bin/env bash
set -euo pipefail

elf="${1:?usage: check-frame-budget-machine.sh ELF}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

symbols="$(mktemp)"
dump="$(mktemp)"
trap 'rm -f "$symbols" "$dump"' EXIT
nm "$elf" > "$symbols"

grep -F ' leanos_frame_budget_mapping_page' "$symbols" >/dev/null || {
  echo "error: frame-budget ELF lacks generated mapping-page policy" >&2
  exit 1
}
if grep -F 'frame_budget_reuse_frame' "$symbols" >/dev/null; then
  echo "error: frame-budget ELF retained static-buffer substitution" >&2
  exit 1
fi

objdump -d -j .user_a_text -j .user_b_text "$elf" > "$dump"

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
grep -Eq 'movzbl[[:space:]]+\(%rax\),%ebx' <<< "$user_b" || {
  echo "error: subject B lacks direct CPL3 first-byte reuse read" >&2
  exit 1
}
grep -Eq 'movzbl[[:space:]]+0xfff\(%rax\),%ecx' <<< "$user_b" || {
  echo "error: subject B lacks direct CPL3 last-byte reuse read" >&2
  exit 1
}

echo "Frame-budget allocator binding and direct CPL3 canary sites passed"
