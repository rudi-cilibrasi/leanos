#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
elf="${1:-build/boot/leanos-inflight-revocation.elf}"
[[ -f "$elf" ]] || {
  echo "error: inflight-revocation ELF is missing: $elf" >&2
  exit 1
}
./scripts/check-inflight-revocation-machine.sh "$elf"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
sed 's/leanos_composite_dispatch_value(/leanos_capability_reuse_demo(/g' \
  boot/kernel.c > "$tmp/old-adapter.c"
set +e
LEANOS_INFLIGHT_REVOCATION_KERNEL_SOURCE="$tmp/old-adapter.c" \
  ./scripts/check-inflight-revocation-machine.sh "$elf" \
  > "$tmp/old-adapter.output" 2>&1
status=$?
set -e
[[ $status -ne 0 ]] &&
  grep -Eq 'lacks generated leanos_composite_dispatch_value|old stateless adapter|must call leanos_composite_dispatch_value' \
    "$tmp/old-adapter.output" || {
  cat "$tmp/old-adapter.output" >&2
  exit 1
}

sed 's/inflight_revocation_state = control & UINT64_C(0xffff);/inflight_revocation_state = LEANOS_COMPOSITE_STATE_INFLIGHT_LINEAGE_REVOKED;/' \
  boot/kernel.c > "$tmp/spliced-state.c"
set +e
LEANOS_INFLIGHT_REVOCATION_KERNEL_SOURCE="$tmp/spliced-state.c" \
  ./scripts/check-inflight-revocation-machine.sh "$elf" \
  > "$tmp/spliced-state.output" 2>&1
status=$?
set -e
[[ $status -ne 0 ]] &&
  grep -Fq 'state token is not derived from generated control' \
    "$tmp/spliced-state.output" || {
  cat "$tmp/spliced-state.output" >&2
  exit 1
}

sed 's/if (value != LEANOS_COMPOSITE_NO_VALUE)/if (value == UINT64_C(0xffffffffffffffff))/' \
  boot/kernel.c > "$tmp/published-handle.c"
set +e
LEANOS_INFLIGHT_REVOCATION_KERNEL_SOURCE="$tmp/published-handle.c" \
  ./scripts/check-inflight-revocation-machine.sh "$elf" \
  > "$tmp/published-handle.output" 2>&1
status=$?
set -e
[[ $status -ne 0 ]] &&
  grep -Fq 'accepts a published handle' "$tmp/published-handle.output" || {
  cat "$tmp/published-handle.output" >&2
  exit 1
}
echo "In-flight revocation final-ELF policy negatives passed"
