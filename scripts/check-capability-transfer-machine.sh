#!/usr/bin/env bash
set -euo pipefail

elf="${1:?usage: check-capability-transfer-machine.sh ELF}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
kernel_source="${LEANOS_CAPABILITY_TRANSFER_KERNEL_SOURCE:-$root/boot/kernel.c}"
assembly_source="${LEANOS_CAPABILITY_TRANSFER_ASSEMBLY_SOURCE:-$root/boot/boot.S}"

for input in "$elf" "$kernel_source" "$assembly_source"; do
  [[ -f "$input" ]] || {
    echo "error: capability-transfer policy input is missing: $input" >&2
    exit 1
  }
done

symbols="$(mktemp)"
dump="$(mktemp)"
trap 'rm -f "$symbols" "$dump"' EXIT
nm "$elf" > "$symbols"
objdump -d "$elf" > "$dump"

for symbol in leanos_composite_dispatch leanos_composite_dispatch_value; do
  grep -Eq " [Tt] ${symbol}$" "$symbols" || {
    echo "error: capability-transfer ELF lacks generated ${symbol}" >&2
    exit 1
  }
done

transfer_source="$(
  sed -n '/if (number >= 26 && number <= 30)/,/fail("capability-transfer-syscall");/p' \
    "$kernel_source"
)"
[[ -n "$transfer_source" ]] || {
  echo "error: capability-transfer machine adapter is missing" >&2
  exit 1
}
for accessor in leanos_composite_dispatch leanos_composite_dispatch_value; do
  [[ "$(grep -Fc "${accessor}(" <<< "$transfer_source")" -eq 2 ]] || {
    echo "error: capability-transfer adapter must call ${accessor} once for the user edge and once for the authoritative switch" >&2
    exit 1
  }
done
grep -Fq 'prestate, command, arg0, arg1, arg2, arg3' \
  <<< "$transfer_source" || {
  echo "error: capability-transfer accessors do not share one immutable input tuple" >&2
  exit 1
}
if grep -Eq 'leanos_(capability_reuse|blocking_ipc|ipc)_demo' \
    <<< "$transfer_source"; then
  echo "error: capability-transfer path calls an old stateless adapter" >&2
  exit 1
fi
if grep -Eq 'static[^;]*(rights|pending|slot|child|parent|generation|mailbox)' \
    <<< "$(sed -n '/#ifdef LEANOS_CAPABILITY_TRANSFER_SCENARIO/,/#endif/p' \
      "$kernel_source")"; then
  echo "error: capability-transfer C path retains shadow authority state" >&2
  exit 1
fi
grep -Fq 'capability_transfer_state = control & UINT64_C(0xffff);' \
  <<< "$transfer_source" || {
  echo "error: capability-transfer state token is not derived from generated control" >&2
  exit 1
}
grep -Fq 'switch_prestate, switch_command, 0, 0, 0, 0' \
  <<< "$transfer_source" || {
  echo "error: capability-transfer subject switch is not generated from one immutable input tuple" >&2
  exit 1
}
grep -Fq 'LEANOS_COMPOSITE_REPLY_BOOT_TRANSFER_SWITCHED' \
  <<< "$transfer_source" || {
  echo "error: capability-transfer subject switch lacks exact generated authorization" >&2
  exit 1
}

handler="$(sed -n '/<syscall_handler>:/,/<timer_handler>:/p' "$dump")"
for accessor in leanos_composite_dispatch leanos_composite_dispatch_value; do
  grep -E "call.*<${accessor}>" <<< "$handler" >/dev/null || {
    echo "error: capability-transfer final ELF lacks ${accessor} call site" >&2
    exit 1
  }
done
for diagnostic in \
  capability-transfer-caller-context \
  capability-transfer-generated-rejection \
  capability-transfer-value-shape \
  capability-transfer-switch-result \
  capability-transfer-syscall; do
  strings "$elf" | grep -Fx "$diagnostic" >/dev/null || {
    echo "error: capability-transfer final ELF lacks fail-closed diagnostic ${diagnostic}" >&2
    exit 1
  }
done

isr80_source="$(sed -n '/^isr80:/,/call syscall_handler/p' "$assembly_source")"
grep -Fq 'mov 72(%rsp), %r9' <<< "$isr80_source" || {
  echo "error: capability-transfer syscall entry drops canonical arg3" >&2
  exit 1
}
symbol_address() {
  awk -v wanted="$1" '$3 == wanted { print "0x" $1; exit }' "$symbols"
}
user_a_start="$(symbol_address user_a_entry)"
user_a_end="$(symbol_address user_a_capability_transfer_end)"
user_b_start="$(symbol_address user_b_entry)"
user_b_end="$(symbol_address user_b_capability_transfer_end)"
for address in "$user_a_start" "$user_a_end" "$user_b_start" "$user_b_end"; do
  [[ -n "$address" ]] || {
    echo "error: capability-transfer subject range symbol is missing" >&2
    exit 1
  }
done
user_a="$(objdump -d --start-address="$user_a_start" \
  --stop-address="$user_a_end" "$elf")"
user_b="$(objdump -d --start-address="$user_b_start" \
  --stop-address="$user_b_end" "$elf")"
[[ "$(grep -Ec 'int[[:space:]]+\$0x80' <<< "$user_a")" -eq 1 ]] || {
  echo "error: capability-transfer subject A syscall inventory drifted" >&2
  exit 1
}
grep -Eq 'mov[[:space:]]+\$0x20001,%[er]?bx' <<< "$user_a" &&
  grep -Eq 'mov[[:space:]]+\$0x20001,%[er]?cx' <<< "$user_a" || {
  echo "error: subject A does not offer its own generation-bound endpoint handle" >&2
  exit 1
}
[[ "$(grep -Ec 'int[[:space:]]+\$0x80' <<< "$user_b")" -eq 4 ]] || {
  echo "error: capability-transfer subject B syscall inventory drifted" >&2
  exit 1
}
grep -Eq 'cmp[[:space:]]+\$0x60003,%rax' <<< "$user_b" &&
  grep -Eq 'mov[[:space:]]+%rax,%r14' <<< "$user_b" &&
  grep -Eq 'mov[[:space:]]+%r14,%rbx' <<< "$user_b" || {
  echo "error: subject B does not use the exact returned generation-bound handle" >&2
  exit 1
}

echo "Capability-transfer generated calls, CPL3 sites, and final-ELF inventory passed"
