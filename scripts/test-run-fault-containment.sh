#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT; touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
${CC:-gcc} -nostdlib -no-pie -Wl,-e,_start -x c -o "$tmp/fault-symbols.elf" - <<'EOF'
char page_map_level_4_a[4096];
char user_a_fault_instruction[8];
char user_a_write_fault_instruction[8];
char user_a_write_target[1];
char user_a_nx_fault_instruction[16];
char user_a_stack_top[1];
void _start(void) {}
EOF
invoke() {
  local mode="$1" scenario="${2:-fault-containment}"
  LEANOS_BOOT_SCENARIO="$scenario" \
  LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
  LEANOS_QEMU="$root/tests/qemu-fixture.sh" LEANOS_QEMU_FIXTURE_MODE="$mode" \
  LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/$mode.serial" \
  LEANOS_FAULT_SNAPSHOT_ARTIFACT="$tmp/$mode.snapshot" \
  LEANOS_FAULT_CONTAINMENT_ELF="$tmp/fault-symbols.elf" \
  ./scripts/run-image.sh "$tmp/image.iso"
}
invoke success >/dev/null 2>&1
LEANOS_BOOT_SCENARIO=fault-readonly-write \
  LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
  LEANOS_QEMU="$root/tests/qemu-fixture.sh" LEANOS_QEMU_FIXTURE_MODE=success \
  LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/write.serial" \
  LEANOS_FAULT_SNAPSHOT_ARTIFACT="$tmp/write.snapshot" \
  LEANOS_FAULT_CONTAINMENT_ELF="$tmp/fault-symbols.elf" \
  ./scripts/run-image.sh "$tmp/image.iso" >/dev/null 2>&1
invoke success fault-nx-execute >/dev/null 2>&1
for mode in fault-nx-wrong-error fault-nx-mapping-permission-drift \
    fault-nx-payload-forged; do
  set +e
  invoke "$mode" fault-nx-execute >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  [[ $status -ne 0 ]] && grep -q 'failure_class=serial-protocol' \
      "$tmp/$mode.output" || {
    cat "$tmp/$mode.output" >&2
    exit 1
  }
done
for spec in \
  'fault-direct-call serial-protocol' \
  'fault-wrong-error serial-protocol' \
  'fault-zero-error serial-protocol' \
  'fault-wrong-cr2 serial-protocol' \
  'fault-wrong-rip serial-protocol' \
  'fault-wrong-access serial-protocol' \
  'fault-wrong-dispatch serial-protocol' \
  'fault-mapping-permission-drift serial-protocol' \
  'fault-snapshot-missing page-fault-snapshot' \
  'fault-snapshot-duplicate page-fault-snapshot' \
  'fault-snapshot-version page-fault-snapshot' \
  'fault-snapshot-rip page-fault-snapshot' \
  'fault-snapshot-authorization page-fault-snapshot' \
  'fault-snapshot-route page-fault-snapshot' \
  'fault-snapshot-reordered page-fault-snapshot' \
  'fault-old-recovery serial-protocol' \
  'fault-stale-cr3 serial-protocol' \
  'fault-cleanup-missing serial-protocol' \
  'fault-a-queued serial-protocol' \
  'fault-attacker-selection serial-protocol' \
  'fault-return-unvalidated serial-protocol' \
  'fault-peer-corrupt serial-protocol' \
  'fault-peer-cleaned serial-protocol' \
  'fault-forged-pass serial-protocol' \
  'fault-reordered serial-protocol' \
  'fault-kernel-relabeled serial-protocol' \
  'fault-global-fail guest-error' \
  'hang timeout' \
  'reset qemu-error' \
  'triple-fault qemu-error'; do
  read -r mode class <<< "$spec"
  set +e; invoke "$mode" >"$tmp/$mode.output" 2>&1; status=$?; set -e
  [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$mode.output" || {
    cat "$tmp/$mode.output" >&2; exit 1;
  }
done
echo "Fault-containment QEMU runner success and negative fixture checks passed"
