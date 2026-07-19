#!/usr/bin/env bash
set -euo pipefail

elf="${1:-build/boot/leanos.elf}"
kernel_source="${LEANOS_ENTRY_KERNEL_SOURCE:-boot/kernel.c}"
boot_source="${LEANOS_ENTRY_BOOT_SOURCE:-boot/boot.S}"
[[ -f "$elf" ]] || { echo "error: missing entry-policy ELF: $elf" >&2; exit 1; }
[[ -f "$kernel_source" && -f "$boot_source" ]] || {
  echo "error: missing entry-policy source snapshot" >&2; exit 1;
}

symbols="$(nm "$elf")"
for symbol in isr6 isr7 isr14 isr32 isr80 authorize_interrupt_entry \
  complete_interrupt_entry extended_state_denial_handler syscall_handler \
  page_fault_handler timer_handler entry_stack boot_stack boot_stack_top; do
  grep -Eq "[[:space:]]${symbol}$" <<<"$symbols" || {
    echo "error: entry manifest symbol missing: $symbol" >&2; exit 1;
  }
done

[[ "$(grep -Ec 'set_gate\(' "$kernel_source")" -eq 8 ]] || {
  echo "error: vector=77 field=present violated=unexpected-installed-gate-count" >&2; exit 1;
}
grep -Fq 'set_gate(6, isr6, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=6 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(7, isr7, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=7 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(14, isr14, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=14 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(32, isr32, 0, 0x8e);' "$kernel_source" || {
  echo "error: vector=32 field=target-or-dpl" >&2; exit 1;
}
grep -Fq 'set_gate(0x80, isr80, 0, 0xee);' "$kernel_source" || {
  echo "error: vector=128 field=target-or-dpl" >&2; exit 1;
}
[[ "$(grep -Ec 'set_gate\([^,]+,[^,]+,[^,]+, 0xee\)' "$kernel_source")" -eq 1 ]] || {
  echo "error: vector=128 field=dpl expected=3 violated=extra-dpl3-gate" >&2; exit 1;
}
grep -Fq 'tss.rsp0 = (uint64_t)__entry_stack_end;' "$kernel_source" || {
  echo "error: vector=128 field=tss.rsp0" >&2; exit 1;
}

source_path="$(sed -n '/^isr80:/,/^\.global isr14/p' "$boot_source")"
source_cleanup="$(grep -n -m1 '^[[:space:]]*clac$' <<<"$source_path" | cut -d: -f1)"
source_normalize="$(grep -n -m1 'NORMALIZE_ENTRY 128, 0' <<<"$source_path" | cut -d: -f1)"
source_handler="$(grep -n -m1 'call syscall_handler' <<<"$source_path" | cut -d: -f1)"
[[ -n "$source_cleanup" && -n "$source_normalize" && -n "$source_handler" &&
   "$source_cleanup" -lt "$source_normalize" && "$source_normalize" -lt "$source_handler" ]] || {
  echo "error: vector=128 path=normalization" >&2; exit 1;
}
source_path="$(sed -n '/^isr32:/,/^\/\* The only boot-reachable CPL3 return/p' "$boot_source")"
grep -q '^[[:space:]]*clac$' <<<"$source_path" || {
  echo "error: vector=32 path=cleanup" >&2; exit 1;
}
source_path="$(sed -n '/^isr14:/,/^\.global isr32/p' "$boot_source")"
grep -q 'mov \$1, %esi' <<<"$source_path" || {
  echo "error: vector=14 field=error-shape" >&2; exit 1;
}
for vector in 6 7; do
  if [[ "$vector" == 6 ]]; then
    source_path="$(sed -n '/^isr6:/,/^\.global isr7/p' "$boot_source")"
  else
    source_path="$(sed -n '/^isr7:/,/^\.global isr80/p' "$boot_source")"
  fi
  source_cleanup="$(grep -n -m1 '^[[:space:]]*clac$' <<<"$source_path" | cut -d: -f1 || true)"
  source_normalize="$(grep -n -m1 "NORMALIZE_ENTRY $vector, 0" <<<"$source_path" | cut -d: -f1 || true)"
  source_handler="$(grep -n -m1 'call extended_state_denial_handler' <<<"$source_path" | cut -d: -f1 || true)"
  [[ -n "$source_cleanup" && -n "$source_normalize" && -n "$source_handler" &&
     "$source_cleanup" -lt "$source_normalize" && "$source_normalize" -lt "$source_handler" ]] || {
    echo "error: vector=$vector path=denial" >&2; exit 1;
  }
done

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
  grep -Eq '(<complete_interrupt_entry>|user_return_epilogue)' <<<"$dis" || {
    echo "error: vector=$vector path=stub violated=entry-latch-not-completed" >&2; exit 1;
  }
  echo "ENTRY-POLICY vector=$vector target=$start_symbol cleanup=AC,DF normalize=shared handler=$handler result=PASS"
}

check_path 128 isr80 isr14 syscall_handler
check_path 14 isr14 isr32 page_fault_handler
check_path 32 isr32 user_return_epilogue timer_handler

check_denial_path() {
  local vector="$1" start_symbol="$2" stop_symbol="$3"
  local start stop dis cleanup normalize operation
  start="$(address "$start_symbol")"; stop="$(address "$stop_symbol")"
  dis="$(objdump -d --no-show-raw-insn --start-address="$start" --stop-address="$stop" "$elf")"
  cleanup="$(grep -n -m1 -E '[[:space:]]clac$' <<<"$dis" | cut -d: -f1)"
  normalize="$(grep -n -m1 'call.*<authorize_interrupt_entry>' <<<"$dis" | cut -d: -f1)"
  operation="$(grep -n -m1 'call.*<extended_state_denial_handler>' <<<"$dis" | cut -d: -f1)"
  grep -n -m1 -E '[[:space:]]cld$' <<<"$dis" >/dev/null || {
    echo "error: vector=$vector path=cleanup field=df" >&2; exit 1;
  }
  [[ -n "$cleanup" && -n "$normalize" && -n "$operation" &&
     "$cleanup" -lt "$normalize" && "$normalize" -lt "$operation" ]] || {
    echo "error: vector=$vector path=denial violated=handler-before-cleanup-or-normalization" >&2
    exit 1
  }
  echo "ENTRY-POLICY vector=$vector target=$start_symbol cleanup=AC,DF normalize=shared handler=fail-stop result=PASS"
}

check_denial_path 6 isr6 isr7
check_denial_path 7 isr7 isr80
epilogue_dis="$(objdump -d --no-show-raw-insn --start-address="$(address user_return_epilogue)" \
  --stop-address="$(address user_return_iretq)" "$elf")"
grep -q 'call.*<validate_user_return>' <<<"$epilogue_dis" || {
  echo "error: ordinary entry path does not reach the reviewed return gate" >&2; exit 1;
}
grep -Fq 'if (ordinary_entry_active) ordinary_entry_active = 0;' "$kernel_source" || {
  echo "error: reviewed return gate does not consume the entry latch" >&2; exit 1;
}

echo "Entry manifest, TSS snapshot, and final-ELF paths passed"
