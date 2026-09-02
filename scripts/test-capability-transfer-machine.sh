#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
elf="${1:-build/boot/leanos-capability-transfer.elf}"
[[ -f "$elf" ]] || {
  echo "error: capability-transfer ELF is missing: $elf" >&2
  exit 1
}
./scripts/check-capability-transfer-machine.sh "$elf"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cp boot/kernel.c "$tmp/kernel.c"
sed 's/leanos_composite_dispatch_value(/leanos_capability_reuse_demo(/g' \
  boot/kernel.c > "$tmp/old-adapter.c"
set +e
LEANOS_CAPABILITY_TRANSFER_KERNEL_SOURCE="$tmp/old-adapter.c" \
  ./scripts/check-capability-transfer-machine.sh "$elf" \
  > "$tmp/old-adapter.output" 2>&1
status=$?
set -e
[[ $status -ne 0 ]] &&
  grep -Eq 'lacks generated leanos_composite_dispatch_value|old stateless adapter|must call leanos_composite_dispatch_value' \
    "$tmp/old-adapter.output" || {
  cat "$tmp/old-adapter.output" >&2
  exit 1
}

sed 's/capability_transfer_state = control & UINT64_C(0xffff);/capability_transfer_state = LEANOS_COMPOSITE_STATE_TRANSFER_ACCEPTED;/' \
  boot/kernel.c > "$tmp/spliced-state.c"
set +e
LEANOS_CAPABILITY_TRANSFER_KERNEL_SOURCE="$tmp/spliced-state.c" \
  ./scripts/check-capability-transfer-machine.sh "$elf" \
  > "$tmp/spliced-state.output" 2>&1
status=$?
set -e
[[ $status -ne 0 ]] &&
  grep -Fq 'state token is not derived from generated control' \
    "$tmp/spliced-state.output" || {
  cat "$tmp/spliced-state.output" >&2
  exit 1
}
echo "Capability-transfer final-ELF policy negatives passed"
