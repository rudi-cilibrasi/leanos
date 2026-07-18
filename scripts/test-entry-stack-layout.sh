#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/stack.S" <<'EOF'
.section .entry.stack,"aw",@nobits
.global entry_stack
entry_stack:
  .skip 16384
EOF
cat >"$tmp/mapped-guard.S" <<'EOF'
.section .entry.guard,"aw",@progbits
  .byte 0
  .skip 4095
EOF
cat >"$tmp/layout.ld" <<'EOF'
SECTIONS {
  . = 1M;
  .entry_stack_guard (NOLOAD) : ALIGN(4K) {
    __entry_stack_guard_start = .;
    KEEP(*(.entry.guard))
    . = __entry_stack_guard_start + 4K;
    __entry_stack_guard_end = .;
  }
  .entry_stack (NOLOAD) : ALIGN(4K) {
    __entry_stack_start = .;
    KEEP(*(.entry.stack))
    __entry_stack_end = .;
  }
}
EOF

gcc -c "$tmp/stack.S" -o "$tmp/stack.o"
gcc -c "$tmp/mapped-guard.S" -o "$tmp/mapped-guard.o"
ld --build-id=none -T "$tmp/layout.ld" -o "$tmp/valid.elf" "$tmp/stack.o"
./scripts/check-entry-stack-layout.sh "$tmp/valid.elf" >/dev/null

run_rejected() {
  local name="$1" diagnostic="$2"
  shift 2
  if ./scripts/check-entry-stack-layout.sh "$tmp/$name.elf" \
      >"$tmp/$name.log" 2>&1; then
    echo "error: ordinary-entry layout fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$diagnostic" "$tmp/$name.log" || {
    echo "error: ordinary-entry layout fixture '$name' lacked '$diagnostic'" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
}

sed -e '/__entry_stack_guard_start =/d' \
  -e 's/\. = __entry_stack_guard_start + 4K;/. += 4K;/' \
  "$tmp/layout.ld" >"$tmp/missing-guard.ld"
ld --build-id=none -T "$tmp/missing-guard.ld" -o "$tmp/missing-guard.elf" \
  "$tmp/stack.o"
run_rejected missing-guard \
  'ordinary-entry layout symbol missing: __entry_stack_guard_start'

sed 's/\.entry_stack_guard (NOLOAD)/.entry_stack_guard/' \
  "$tmp/layout.ld" >"$tmp/mapped-guard.ld"
ld --build-id=none -T "$tmp/mapped-guard.ld" -o "$tmp/mapped-guard.elf" \
  "$tmp/stack.o" "$tmp/mapped-guard.o"
run_rejected mapped-guard \
  'ordinary-entry section .entry_stack_guard must be NOBITS, found PROGBITS'

sed 's/__entry_stack_end = \.;/__entry_stack_end = . - 8;/' \
  "$tmp/layout.ld" >"$tmp/misaligned-top.ld"
ld --build-id=none -T "$tmp/misaligned-top.ld" -o "$tmp/misaligned-top.elf" \
  "$tmp/stack.o"
run_rejected misaligned-top \
  'ordinary-entry canonical top is not 16-byte aligned'

echo "ordinary-entry final-ELF layout fixtures passed"
