#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fixture_root="$(mktemp -d)"
trap 'rm -rf "$fixture_root"' EXIT

syscall_fixture="$fixture_root/Syscall.lean"
ipc_fixture="$fixture_root/IPCSyscall.lean"
log="$fixture_root/check.log"
cp LeanOS/Syscall.lean "$syscall_fixture"
cp LeanOS/IPCSyscall.lean "$ipc_fixture"

run_fixture() {
  CAPABILITY_SYSCALL_SOURCE="$syscall_fixture" \
    CAPABILITY_IPC_SOURCE="$ipc_fixture" \
    ./scripts/check-capability-boundaries.sh
}

run_fixture >/dev/null

sed -i \
  's/\.map call\.arg0 call\.arg1\.toNat permissions/.map call.arg0.toNat call.arg1.toNat permissions/' \
  "$syscall_fixture"
if run_fixture >"$log" 2>&1; then
  echo "error: truncating map-handle fixture unexpectedly passed" >&2
  exit 1
fi
if ! grep -q 'truncating raw-slot map decoder' "$log"; then
  cat "$log" >&2
  echo "error: truncating map-handle fixture lacked the expected diagnostic" >&2
  exit 1
fi

cp LeanOS/Syscall.lean "$syscall_fixture"
sed -i '0,/CapabilityHandle\.resolveCurrent/s//Capability.lookup/' "$ipc_fixture"
if run_fixture >"$log" 2>&1; then
  echo "error: raw IPC lookup fixture unexpectedly passed" >&2
  exit 1
fi
if ! grep -q 'raw-slot capability lookup in boot-reachable IPC dispatch' "$log"; then
  cat "$log" >&2
  echo "error: raw IPC lookup fixture lacked the expected diagnostic" >&2
  exit 1
fi

echo "Capability boundary negative regression checks passed"
