#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build=build/boot-handoff-host
rm -rf "$build"
mkdir -p "$build"

lake build LeanOS.BootMemoryMapDecoderABI

prefix="$(lake env lean --print-prefix)"
for module in FrameAllocator BootMemoryMap BootMemoryMapDecoder BootMemoryMapDecoderABI; do
  lake env leanc -O2 -ffunction-sections -fdata-sections -I"$prefix/include" \
    -c ".lake/build/ir/LeanOS/$module.c" -o "$build/$module.o"
done
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$prefix/include" \
  -c tests/boot-handoff-host.c -o "$build/host.o"
lake env leanc -Wl,--gc-sections \
  "$build/host.o" "$build/FrameAllocator.o" "$build/BootMemoryMap.o" \
  "$build/BootMemoryMapDecoder.o" "$build/BootMemoryMapDecoderABI.o" \
  -o "$build/host"
"$build/host" | tee "$build/results.txt"
