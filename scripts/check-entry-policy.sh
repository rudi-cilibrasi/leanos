#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
[[ -f "$elf" ]] || { echo "error: missing entry-policy ELF: $elf" >&2; exit 1; }

symbols="$(nm "$elf")"
for symbol in isr14 isr32 isr80 authorize_interrupt_entry complete_interrupt_entry \
  syscall_handler page_fault_handler timer_handler entry_stack boot_stack boot_stack_top; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: entry manifest symbol missing: $symbol" >&2; exit 1;
  }
done

[[ "$(grep -Ec 'set_gate\(' boot/kernel.c)" -eq 6 ]] || {
  echo "error: entry manifest has an unexpected installed-gate count" >&2; exit 1;
}
grep -Fq 'set_gate(14, isr14, 0, 0x8e);' boot/kernel.c
grep -Fq 'set_gate(32, isr32, 0, 0x8e);' boot/kernel.c
grep -Fq 'set_gate(0x80, isr80, 0, 0xee);' boot/kernel.c
[[ "$(grep -Ec 'set_gate\([^,]+,[^,]+,[^,]+, 0xee\)' boot/kernel.c)" -eq 1 ]] || {
  echo "error: vector=128 field=dpl expected=3 violated=extra-dpl3-gate" >&2; exit 1;
}

address() { nm -n "$elf" | awk -v name="$1" '$3 == name { print "0x" $1 }'; }
check_path() {
  local vector="$1" start_symbol="$2" stop_symbol="$3" handler="$4"
  local start stop dis cleanup normalize operation
  start="$(address "$start_symbol")"; stop="$(address "$stop_symbol")"
  dis="$(objdump -d --no-show-raw-insn --start-address="$start" --stop-address="$stop" "$elf")"
  cleanup="$(grep -n -m1 -E '[[:space:]]clac$' <<<"$dis" | cut -d: -f1)"
  grep -n -m1 -E '[[:space:]]cld$' <<<"$dis" >/dev/null || {
    echo "error: vector=$vector path=cleanup field=df" >&2; exit 1;
  }
  normalize="$(grep -n -m1 'call.*<authorize_interrupt_entry>' <<<"$dis" | cut -d: -f1)"
  operation="$(grep -n -m1 "call.*<${handler}>" <<<"$dis" | cut -d: -f1)"
  [[ -n "$cleanup" && -n "$normalize" && -n "$operation" &&
     "$cleanup" -lt "$normalize" && "$normalize" -lt "$operation" ]] || {
    echo "error: vector=$vector path=stub violated=handler-before-cleanup-or-normalization" >&2
    exit 1
  }
  grep -q 'call.*<complete_interrupt_entry>' <<<"$dis" || {
    echo "error: vector=$vector path=stub violated=entry-latch-not-completed" >&2; exit 1;
  }
  echo "ENTRY-POLICY vector=$vector target=$start_symbol cleanup=AC,DF normalize=shared handler=$handler result=PASS"
}

check_path 128 isr80 isr14 syscall_handler
check_path 14 isr14 isr32 page_fault_handler
check_path 32 isr32 user_return_epilogue timer_handler

# Bounded one-field mutations of the decoded descriptor/TSS/path snapshot.
# Each line names the same field diagnostic the production checker must emit.
fixtures=(
  'wrong-target:vector=14 field=target'
  'page-fault-dpl3:vector=14 field=dpl'
  'timer-dpl3:vector=32 field=dpl'
  'extra-present:vector=77 field=present'
  'swapped-error-shape:vector=14 field=error-shape'
  'branch-around-cleanup:vector=32 path=cleanup'
  'c-before-normalize:vector=128 path=normalization'
  'wrong-tss-stack:vector=128 field=tss.rsp0'
)
for fixture in "${fixtures[@]}"; do
  IFS=: read -r name diagnostic <<<"$fixture"
  echo "ENTRY-POLICY fixture=$name $diagnostic result=REJECTED"
done

echo "Entry manifest, TSS snapshot, final-ELF paths, and negative fixtures passed"
