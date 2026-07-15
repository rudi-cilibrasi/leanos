#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
build=build/oracle
rm -rf "$build"; mkdir -p "$build"
./scripts/generate-oracle.sh "$build"
lake env lean --c="$build/KernelTransition.c" LeanOS/KernelTransition.lean
lake env lean --c="$build/Syscall.c" LeanOS/Syscall.lean
lake env lean --c="$build/IPCSyscall.c" LeanOS/IPCSyscall.lean
prefix="$(lake env lean --print-prefix)"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/KernelTransition.c" -o "$build/KernelTransition.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/Syscall.c" -o "$build/Syscall.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/IPCSyscall.c" -o "$build/IPCSyscall.o"
cc -std=c11 -Wall -Wextra -Werror -I"$build" -c tests/oracle-host.c -o "$build/host.o"
cc -Wl,--gc-sections "$build/host.o" "$build/KernelTransition.o" "$build/Syscall.o" "$build/IPCSyscall.o" -o "$build/host"
"$build/host" > "$build/host-results.txt"
[[ "$(wc -l < "$build/host-results.txt")" -eq 13 ]]
echo "Hosted generated-code oracle replay passed (13 vectors)"
