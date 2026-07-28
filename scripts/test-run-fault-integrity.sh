#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"
cat > "$tmp/symbols.c" <<'EOF'
char user_a_nx_fault_instruction[16];
void _start(void) {}
EOF
gcc -nostdlib -static "$tmp/symbols.c" -o "$tmp/symbols.elf"

invoke() {
  local probe="$1" mode="$2"
  LEANOS_QEMU="$root/tests/qemu-fault-integrity-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$mode" LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_FAULT_INTEGRITY_PROBE="$probe" \
    LEANOS_FAULT_INTEGRITY_ELF="$tmp/symbols.elf" \
    LEANOS_SERIAL_LOG="$tmp/${probe}-${mode}.serial" \
    LEANOS_FAULT_TERMINAL_ARTIFACT="$tmp/${probe}-${mode}.terminal" \
    ./scripts/run-fault-integrity.sh "$tmp/image.iso"
}

for probe in reserved-bit walk-mismatch; do
  invoke "$probe" success >/dev/null 2>&1
done
for spec in \
  'missing terminal-record' \
  'duplicate terminal-record' \
  'wrong-field terminal-record' \
  'containment forbidden-record' \
  'cleanup forbidden-record' \
  'peer-dispatch forbidden-record' \
  'user-return forbidden-record' \
  'normal-success normal-success' \
  'generic-error guest-error' \
  'reset qemu-error' \
  'hang timeout'; do
  read -r mode class <<< "$spec"
  set +e
  invoke reserved-bit "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -q "failure_class=$class" "$tmp/$mode.output"; then
    cat "$tmp/$mode.output" >&2
    exit 1
  fi
done

echo "Fault-integrity runner success and controlled negative fixture checks passed"
