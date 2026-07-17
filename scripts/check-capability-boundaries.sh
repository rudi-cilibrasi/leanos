#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

syscall_source="${CAPABILITY_SYSCALL_SOURCE:-LeanOS/Syscall.lean}"
ipc_source="${CAPABILITY_IPC_SOURCE:-LeanOS/IPCSyscall.lean}"

failure=0

require_literal() {
  local file="$1"
  local literal="$2"
  local description="$3"
  if ! grep -Fq -- "$literal" "$file"; then
    echo "error: ${file} lost ${description}" >&2
    failure=1
  fi
}

reject_pattern() {
  local file="$1"
  local pattern="$2"
  local description="$3"
  if grep -En -- "$pattern" "$file"; then
    echo "error: ${file} contains ${description}" >&2
    failure=1
  fi
}

syscall_dispatch="$(mktemp)"
ipc_dispatch="$(mktemp)"
trap 'rm -f "$syscall_dispatch" "$ipc_dispatch"' EXIT

sed -n '/^def dispatchDecoded /,/^def dispatch /p' "$syscall_source" >"$syscall_dispatch"
sed -n '/^def dispatch /,/^theorem dispatch_preserves/p' "$ipc_source" >"$ipc_dispatch"

require_literal "$syscall_source" \
  '| some permissions => .ok (.map call.arg0 call.arg1.toNat permissions)' \
  'the opaque map-handle word at decode'
require_literal "$syscall_dispatch" 'CapabilityHandle.resolveCurrent' \
  'generation-checked map resolution'
require_literal "$syscall_dispatch" 'resolution.handle.slot' \
  'post-resolution internal-slot dispatch'
reject_pattern "$syscall_source" '\.map[[:space:]]+call\.arg0\.toNat' \
  'a truncating raw-slot map decoder'
reject_pattern "$syscall_dispatch" 'Capability\.lookup|handleWord\.toNat' \
  'a raw-slot capability lookup in boot-reachable map dispatch'

require_literal "$ipc_source" '| send (handleWord : UInt64)' \
  'an opaque send-handle word'
require_literal "$ipc_source" '| receive (handleWord : UInt64)' \
  'an opaque receive-handle word'
require_literal "$ipc_dispatch" 'CapabilityHandle.resolveCurrent' \
  'generation-checked endpoint resolution'
require_literal "$ipc_dispatch" 'resolution.handle.slot' \
  'post-resolution internal-slot dispatch'
reject_pattern "$ipc_dispatch" 'Capability\.lookup|handleWord\.toNat' \
  'a raw-slot capability lookup in boot-reachable IPC dispatch'

if (( failure != 0 )); then
  exit 1
fi

echo "Boot-reachable capability boundary checks passed"
