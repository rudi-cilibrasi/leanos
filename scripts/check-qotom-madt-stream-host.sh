#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
python3 scripts/test-qotom-madt-stream.py
python3 scripts/test-qotom-madt-finish.py
bash scripts/check-qotom-madt-stream-object.sh
build=build/qotom-madt-stream
prefix="$(lean --print-prefix)"
for mode in ordinary sanitized; do
  flags=(-O2 -ffunction-sections -fdata-sections -fno-pie)
  if [[ "$mode" == sanitized ]]; then
    flags+=(-fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer)
  fi
  "${CC:-gcc}" "${flags[@]}" -I"$prefix/include" -I"$build" \
    "$build/QotomMadtStream.c" tests/qotom-madt-stream-host.c \
    -no-pie -Wl,--gc-sections -o "$build/host-$mode"
  ASAN_OPTIONS=detect_leaks=1 UBSAN_OPTIONS=halt_on_error=1 \
    "$build/host-$mode" > "$build/results-$mode.txt"
done
cmp "$build/results-ordinary.txt" "$build/results-sanitized.txt"
printf '%s\n' 'PASS generated-C ordinary/sanitized scalar MADT replay'
