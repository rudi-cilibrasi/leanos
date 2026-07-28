#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
build=build/oracle
rm -rf "$build"; mkdir -p "$build"
./scripts/generate-oracle.sh "$build"
lake env lean --c="$build/KernelTransition.c" LeanOS/KernelTransition.lean
lake env lean --c="$build/Syscall.c" LeanOS/Syscall.lean
lake env lean --c="$build/IPCSyscall.c" LeanOS/IPCSyscall.lean
lake env lean --c="$build/Preemption.c" LeanOS/Preemption.lean
lake env lean --c="$build/BootMemoryMapStreamAuthority.c" \
  LeanOS/BootMemoryMapStreamAuthority.lean
lake env lean --c="$build/Interrupt.c" LeanOS/Interrupt.lean
lake env lean --c="$build/InterruptEntry.c" LeanOS/InterruptEntry.lean
lake env lean --c="$build/BlockingIPC.c" LeanOS/BlockingIPC.lean
lake env lean --c="$build/CapabilityReuse.c" LeanOS/CapabilityReuse.lean
lake env lean --c="$build/ExtendedState.c" LeanOS/ExtendedState.lean
lake env lean --c="$build/PrivilegeEntryControl.c" LeanOS/PrivilegeEntryControl.lean
lake env lean --c="$build/FaultDispatch.c" LeanOS/FaultDispatch.lean
lake env lean --c="$build/DirectPortIO.c" LeanOS/DirectPortIO.lean
lake env lean --c="$build/StaleTranslation.c" LeanOS/StaleTranslation.lean
lake env lean --c="$build/CompositeDispatcher.c" LeanOS/CompositeDispatcher.lean
prefix="$(lake env lean --print-prefix)"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/KernelTransition.c" -o "$build/KernelTransition.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/Syscall.c" -o "$build/Syscall.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/IPCSyscall.c" -o "$build/IPCSyscall.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/Preemption.c" -o "$build/Preemption.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/BootMemoryMapStreamAuthority.c" \
  -o "$build/BootMemoryMapStreamAuthority.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/Interrupt.c" -o "$build/Interrupt.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/InterruptEntry.c" -o "$build/InterruptEntry.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/BlockingIPC.c" -o "$build/BlockingIPC.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/CapabilityReuse.c" -o "$build/CapabilityReuse.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/ExtendedState.c" -o "$build/ExtendedState.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/PrivilegeEntryControl.c" \
  -o "$build/PrivilegeEntryControl.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/FaultDispatch.c" -o "$build/FaultDispatch.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/DirectPortIO.c" -o "$build/DirectPortIO.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/StaleTranslation.c" -o "$build/StaleTranslation.o"
cc -std=c11 -I"$prefix/include" -I"$build" \
  -ffunction-sections -fdata-sections -c "$build/CompositeDispatcher.c" \
  -o "$build/CompositeDispatcher.o"
objects=(
  "$build/KernelTransition.o"
  "$build/Syscall.o"
  "$build/IPCSyscall.o"
  "$build/Preemption.o"
  "$build/BootMemoryMapStreamAuthority.o"
  "$build/Interrupt.o"
  "$build/InterruptEntry.o"
  "$build/BlockingIPC.o"
  "$build/CapabilityReuse.o"
  "$build/ExtendedState.o"
  "$build/PrivilegeEntryControl.o"
  "$build/FaultDispatch.o"
  "$build/DirectPortIO.o"
  "$build/StaleTranslation.o"
  "$build/CompositeDispatcher.o"
)
compile_host() {
  local name="$1"
  local define="${2:-}"
  local flags=(-std=c11 -Wall -Wextra -Werror -I"$build" -Iinclude)
  [[ -z "$define" ]] || flags+=("-D$define")
  cc "${flags[@]}" -c tests/oracle-host.c -o "$build/$name.o"
  cc -Wl,--gc-sections "$build/$name.o" "${objects[@]}" -o "$build/$name"
}
compile_host host
"$build/host" > "$build/host-results.txt"
[[ "$(wc -l < "$build/host-results.txt")" -eq 314 ]]

fixtures=(
  "truncated:LEANOS_FIXTURE_COMPOSITE_TRUNCATED:oracle malformed arity"
  "output-corruption:LEANOS_FIXTURE_COMPOSITE_OUTPUT_CORRUPTION:oracle mismatch"
  "old-stateless:LEANOS_FIXTURE_COMPOSITE_OLD_STATELESS:oracle mismatch"
  "wrong-version:LEANOS_FIXTURE_COMPOSITE_WRONG_VERSION:field=reply"
  "reserved-bits:LEANOS_FIXTURE_COMPOSITE_RESERVED_BITS:field=reply"
  "stale-replay:LEANOS_FIXTURE_COMPOSITE_STALE_REPLAY:field=reply"
  "forged-context:LEANOS_FIXTURE_COMPOSITE_FORGED_CONTEXT:field=reply"
  "handle-corruption:LEANOS_FIXTURE_COMPOSITE_HANDLE_CORRUPTION:field=reply"
)
: > "$build/negative-fixtures.tsv"
for fixture in "${fixtures[@]}"; do
  IFS=: read -r name define diagnostic <<< "$fixture"
  compile_host "host-$name" "$define"
  if "$build/host-$name" > "$build/host-$name.txt" 2>&1; then
    echo "error: composite oracle fixture '$name' unexpectedly passed" >&2
    exit 1
  fi
  grep -q "$diagnostic" "$build/host-$name.txt" || {
    echo "error: composite oracle fixture '$name' lacked '$diagnostic'" >&2
    exit 1
  }
  printf '%s\t%s\t%s\n' "$name" "$define" "$diagnostic" \
    >> "$build/negative-fixtures.tsv"
done

{
  printf 'schema\tleanos-oracle-evidence-v1\n'
  printf 'source_revision\t%s\n' "$(git rev-parse HEAD)"
  printf 'generated_c_flags\t%s\n' \
    "-std=c11 -I<lean-prefix>/include -Ibuild/oracle -ffunction-sections -fdata-sections"
  printf 'host_c_flags\t%s\n' \
    "-std=c11 -Wall -Wextra -Werror -Ibuild/oracle -Iinclude"
  printf 'link_flags\t%s\n' "-Wl,--gc-sections"
  printf 'lean_version\t%s\n' "$(lake env lean --version | head -n 1)"
  printf 'cc_version\t%s\n' "$(cc --version | head -n 1)"
} > "$build/toolchain-and-flags.tsv"

{
  printf 'schema\tleanos-oracle-manifest-v1\n'
  printf 'source_revision\t%s\n' "$(git rev-parse HEAD)"
  sha256sum \
    LeanOS/CompositeDispatcher.lean \
    "$build/CompositeDispatcher.c" \
    include/leanos/composite-dispatcher.h \
    "$build/corpus.tsv" \
    "$build/host-results.txt" \
    "$build/negative-fixtures.tsv" \
    "$build/toolchain-and-flags.tsv"
} > "$build/manifest.tsv"

echo "Hosted generated-code oracle replay passed (314 vectors, 8 negative fixtures)"
