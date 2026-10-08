#!/usr/bin/env bash
# The assembly-window inventory (issue #477) passes on the built image and
# rejects an added window without a row and a size drift.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
build="${1:-build/boot}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 scripts/check-asm-windows.py --lane gcc "$build/boot.o" "$build/leanos.elf" >/dev/null

# An added global in the entry text that executes a privileged instruction.
{ cat boot/boot.S; printf '.section .text,"ax",@progbits\n.global unreviewed_window\nunreviewed_window:\n    cli\n    hlt\n'; } \
  >"$tmp/boot.S"
gcc -m64 -ffreestanding -I"$build" -Iinclude -c "$tmp/boot.S" -o "$tmp/boot.o"
if python3 scripts/check-asm-windows.py --lane gcc --source "$tmp/boot.S" "$tmp/boot.o" \
    >"$tmp/added.log" 2>&1; then
  echo "error: inventory accepted an added window without a row" >&2; exit 1
fi
grep -q "unreviewed_window has no row" "$tmp/added.log"

# A size drift: the recorded size of one window no longer matches.
awk -F '\t' 'BEGIN { OFS = FS } $1 == "isr80_cld" { $3 = $3 + 1 } { print }' \
  scripts/asm-windows.tsv >"$tmp/drift.tsv"
if python3 scripts/check-asm-windows.py --lane gcc --table "$tmp/drift.tsv" "$build/boot.o" \
    >"$tmp/drift.log" 2>&1; then
  echo "error: inventory accepted a window size drift" >&2; exit 1
fi
grep -q "isr80_cld is .* bytes in the gcc lane" "$tmp/drift.log"
echo "assembly-window inventory rejects an unlisted window and a size drift"
