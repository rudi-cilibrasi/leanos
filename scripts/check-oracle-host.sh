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
  local flags=(-std=c11 -Wall -Wextra -Werror -I"$build")
  [[ -z "$define" ]] || flags+=("-D$define")
  cc "${flags[@]}" -c tests/oracle-host.c -o "$build/$name.o"
  cc -Wl,--gc-sections "$build/$name.o" "${objects[@]}" -o "$build/$name"
}
compile_host host
"$build/host" > "$build/host-results.txt"
[[ "$(wc -l < "$build/host-results.txt")" -eq 309 ]]

fixtures=(
  "truncated:LEANOS_FIXTURE_COMPOSITE_TRUNCATED:oracle malformed arity"
  "output-corruption:LEANOS_FIXTURE_COMPOSITE_OUTPUT_CORRUPTION:oracle mismatch"
  "old-stateless:LEANOS_FIXTURE_COMPOSITE_OLD_STATELESS:oracle mismatch"
)
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
done

echo "Hosted generated-code oracle replay passed (309 vectors, 3 negative fixtures)"
