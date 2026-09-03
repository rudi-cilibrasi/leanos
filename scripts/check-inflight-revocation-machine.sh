#!/usr/bin/env bash
set -euo pipefail

elf="${1:?usage: check-inflight-revocation-machine.sh ELF}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
kernel_source="${LEANOS_INFLIGHT_REVOCATION_KERNEL_SOURCE:-$root/boot/kernel.c}"
assembly_source="${LEANOS_INFLIGHT_REVOCATION_ASSEMBLY_SOURCE:-$root/boot/boot.S}"

for input in "$elf" "$kernel_source" "$assembly_source"; do
  [[ -f "$input" ]] || {
    echo "error: inflight-revocation policy input is missing: $input" >&2
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
    echo "error: inflight-revocation ELF lacks generated ${symbol}" >&2
    exit 1
  }
done

revocation_source="$(
  sed -n '/if (number >= 31 && number <= 40)/,/fail("inflight-revocation-syscall");/p' \
    "$kernel_source"
)"
[[ -n "$revocation_source" ]] || {
  echo "error: inflight-revocation machine adapter is missing" >&2
  exit 1
}
for accessor in leanos_composite_dispatch leanos_composite_dispatch_value; do
  [[ "$(grep -Fc "${accessor}(" <<< "$revocation_source")" -eq 2 ]] || {
    echo "error: inflight-revocation adapter must call ${accessor} once for the user edge and once for the authoritative switch" >&2
    exit 1
  }
done
grep -Fq 'prestate, command, arg0, arg1, arg2, arg3' \
  <<< "$revocation_source" || {
  echo "error: inflight-revocation accessors do not share one immutable input tuple" >&2
  exit 1
}
if grep -Eq 'leanos_(capability_reuse|blocking_ipc|ipc)_demo' \
    <<< "$revocation_source"; then
  echo "error: inflight-revocation path calls an old stateless adapter" >&2
  exit 1
fi
if grep -Eq 'static[^;]*(rights|pending|slot|child|parent|generation|mailbox|lineage|root)' \
    <<< "$(sed -n '/#ifdef LEANOS_INFLIGHT_REVOCATION_SCENARIO/,/#endif/p' \
      "$kernel_source")"; then
  echo "error: inflight-revocation C path retains shadow authority state" >&2
  exit 1
fi
grep -Fq 'inflight_revocation_state = control & UINT64_C(0xffff);' \
  <<< "$revocation_source" || {
  echo "error: inflight-revocation state token is not derived from generated control" >&2
  exit 1
}
grep -Fq 'if (value != LEANOS_COMPOSITE_NO_VALUE)' <<< "$revocation_source" || {
  echo "error: inflight-revocation adapter accepts a published handle" >&2
  exit 1
}
grep -Fq 'switch_prestate, switch_command, 0, 0, 0, 0' \
  <<< "$revocation_source" || {
  echo "error: inflight-revocation subject switch is not generated from one immutable input tuple" >&2
  exit 1
}
grep -Fq 'LEANOS_COMPOSITE_REPLY_INFLIGHT_SUBJECT_TWO_RESTORED' \
  <<< "$revocation_source" || {
  echo "error: inflight-revocation subject switch lacks exact generated authorization" >&2
  exit 1
}
grep -Fq 'LEANOS_COMPOSITE_REPLY_INFLIGHT_LINEAGE_REVOKED' \
  <<< "$revocation_source" || {
  echo "error: inflight-revocation adapter does not require the exact accepted revocation reply" >&2
  exit 1
}

handler="$(sed -n '/<syscall_handler>:/,/<timer_handler>:/p' "$dump")"
for accessor in leanos_composite_dispatch leanos_composite_dispatch_value; do
  grep -E "call.*<${accessor}>" <<< "$handler" >/dev/null || {
    echo "error: inflight-revocation final ELF lacks ${accessor} call site" >&2
    exit 1
  }
done
for diagnostic in \
  inflight-revocation-caller-context \
  inflight-revocation-generated-rejection \
  inflight-revocation-value-shape \
  inflight-revocation-edge-result \
  inflight-revocation-switch-result \
  inflight-revocation-syscall; do
  strings "$elf" | grep -Fx "$diagnostic" >/dev/null || {
    echo "error: inflight-revocation final ELF lacks fail-closed diagnostic ${diagnostic}" >&2
    exit 1
  }
done

isr80_source="$(sed -n '/^isr80:/,/call syscall_handler/p' "$assembly_source")"
grep -Fq 'mov 72(%rsp), %r9' <<< "$isr80_source" || {
  echo "error: inflight-revocation syscall entry drops canonical arg3" >&2
  exit 1
}
symbol_address() {
  awk -v wanted="$1" '$3 == wanted { print "0x" $1; exit }' "$symbols"
}
user_a_start="$(symbol_address user_a_entry)"
user_a_end="$(symbol_address user_a_inflight_revocation_end)"
user_b_start="$(symbol_address user_b_entry)"
user_b_end="$(symbol_address user_b_inflight_revocation_end)"
for address in "$user_a_start" "$user_a_end" "$user_b_start" "$user_b_end"; do
  [[ -n "$address" ]] || {
    echo "error: inflight-revocation subject range symbol is missing" >&2
    exit 1
  }
done
user_a="$(objdump -d --start-address="$user_a_start" \
  --stop-address="$user_a_end" "$elf")"
user_b="$(objdump -d --start-address="$user_b_start" \
  --stop-address="$user_b_end" "$elf")"
[[ "$(grep -Ec 'int[[:space:]]+\$0x80' <<< "$user_a")" -eq 6 ]] || {
  echo "error: inflight-revocation subject A syscall inventory drifted" >&2
  exit 1
}
grep -Eq 'mov[[:space:]]+\$0x20001,%[er]?bx' <<< "$user_a" &&
  grep -Eq 'mov[[:space:]]+\$0x20001,%[er]?cx' <<< "$user_a" || {
  echo "error: subject A does not offer its own generation-bound endpoint handle" >&2
  exit 1
}
[[ "$(grep -Ec 'test[[:space:]]+%rax,%rax' <<< "$user_a")" -eq 5 ]] || {
  echo "error: subject A does not check every no-value reply before continuing" >&2
  exit 1
}
[[ "$(grep -Ec 'int[[:space:]]+\$0x80' <<< "$user_b")" -eq 4 ]] || {
  echo "error: inflight-revocation subject B syscall inventory drifted" >&2
  exit 1
}
grep -Eq 'mov[[:space:]]+\$0x30000,%[er]?bx' <<< "$user_b" &&
  grep -Eq 'mov[[:space:]]+\$0x70003,%[er]?bx' <<< "$user_b" &&
  grep -Eq 'mov[[:space:]]+\$0x80003,%[er]?bx' <<< "$user_b" || {
  echo "error: subject B does not present the receipt endpoint, the canceled handle, and the replacement handle as full-width words" >&2
  exit 1
}
[[ "$(grep -Ec 'test[[:space:]]+%rax,%rax' <<< "$user_b")" -eq 3 ]] || {
  echo "error: subject B does not refuse a delivered handle before continuing" >&2
  exit 1
}

echo "In-flight revocation generated calls, CPL3 sites, and final-ELF inventory passed"
