#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
build=build/boot-memory-full-projection
rm -rf "$build"
mkdir -p "$build/pass1" "$build/pass2"

rich_run="$(
  sed -n '/^def run (input : Input)/,/^structure Projection where/p' \
    LeanOS/BootMemoryMapFullProjectionABI.lean
)"
for required in 'BootMemoryMapDecoder.decode input' \
  'BootReservation.initializeAllocator decoded.handoff manifest' \
  'FrameAllocator.allocate reserved.allocator owner'; do
  grep -Fq "$required" <<<"$rich_run" || {
    echo "error: full projection source omits exact rich transition: $required" >&2
    exit 1
  }
done
if grep -Eq 'StreamAuthority|manifestCandidate|selectFrame|publishAuthority' \
    <<<"$rich_run"; then
  echo "error: full projection source retained a parallel scalar decision" >&2
  exit 1
fi

lake build LeanOS.BootMemoryMapFullProjectionABI
prefix="$(lake env lean --print-prefix)"
modules=(
  BootInterruptPhase
  BootTopology
  InterruptEntry
  Interrupt
  X86PageTable
  SubjectLifecycle
  VirtualMapping
  EndpointIPC
  MemoryLifecycle
  CapabilityHandle
  FrameAllocator
  Capability
  BootMemoryMap
  BootMemoryMapDecoder
  BootReservation
  BootMemoryMapFullProjectionABI
)
cflags=(-O2 -ffunction-sections -fdata-sections -I"$prefix/include")

for pass in pass1 pass2; do
  objects=()
  for module in "${modules[@]}"; do
    lake env leanc "${cflags[@]}" \
      -c ".lake/build/ir/LeanOS/${module}.c" \
      -o "$build/$pass/${module}.o"
    objects+=("$build/$pass/${module}.o")
  done
  cc -std=c11 -O2 -Wall -Wextra -Werror -I"$prefix/include" \
    -ffunction-sections -fdata-sections \
    -c tests/boot-memory-full-projection-host.c -o "$build/$pass/host.o"
  lake env leanc -Wl,--gc-sections -Wl,--build-id=none \
    "$build/$pass/host.o" \
    "${objects[@]}" \
    -o "$build/$pass/full-projection.elf"
done

for module in "${modules[@]}"; do
  cmp "$build/pass1/${module}.o" "$build/pass2/${module}.o"
done
cmp "$build/pass1/host.o" "$build/pass2/host.o"
cmp "$build/pass1/full-projection.elf" "$build/pass2/full-projection.elf"

symbols="$(nm "$build/pass1/full-projection.elf")"
grep -Eq ' [Tt] leanos_boot_full_projection_fixture_query$' <<<"$symbols" || {
  echo "error: full boot-memory projection ELF omits its sole rich export" >&2
  exit 1
}
for forbidden in leanos_boot_handoff_query leanos_boot_handoff_fixture_query \
  leanos_boot_decode_init leanos_boot_decode_step leanos_boot_manifest_candidate \
  leanos_boot_manifest_start leanos_boot_select_frame \
  leanos_boot_consume_exact_projection leanos_boot_publish_authority \
  leanos_boot_allocation_check; do
  if grep -Eq " [Tt] ${forbidden}$" <<<"$symbols"; then
    echo "error: full boot-memory projection ELF retained parallel authority $forbidden" >&2
    exit 1
  fi
done

cp .lake/build/ir/LeanOS/BootMemoryMapFullProjectionABI.c "$build/generated.c"
nm -n "$build/pass1/full-projection.elf" >"$build/symbols.txt"
readelf -hSW "$build/pass1/full-projection.elf" >"$build/readelf.txt"
objdump -d --no-show-raw-insn "$build/pass1/full-projection.elf" \
  >"$build/disassembly.txt"
sha256sum "$build/generated.c" "$build/pass1/full-projection.elf" \
  tests/boot-memory-full-projection-host.c >"$build/SHA256SUMS"

"$build/pass1/full-projection.elf" | tee "$build/results.txt"
echo "Reproducible generated-C/ELF full boot-memory projection passed"
