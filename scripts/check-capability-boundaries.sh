#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

syscall_source="${CAPABILITY_SYSCALL_SOURCE:-LeanOS/Syscall.lean}"
ipc_source="${CAPABILITY_IPC_SOURCE:-LeanOS/IPCSyscall.lean}"
blocking_source="${CAPABILITY_BLOCKING_SOURCE:-LeanOS/BlockingIPC.lean}"

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
blocking_dispatch="$(mktemp)"
blocking_revoke="$(mktemp)"
blocking_subtree="$(mktemp)"
trap 'rm -f "$syscall_dispatch" "$ipc_dispatch" "$blocking_dispatch" "$blocking_revoke" "$blocking_subtree"' EXIT

sed -n '/^def dispatchDecoded /,/^def dispatch /p' "$syscall_source" >"$syscall_dispatch"
sed -n '/^def dispatch /,/^theorem dispatch_preserves/p' "$ipc_source" >"$ipc_dispatch"
sed -n '/^def receiveOrBlockWord /,/^def cancelSubject /p' "$blocking_source" >"$blocking_dispatch"
sed -n '/^def revokeWords /,/^\/-- An accepted blocking-IPC revocation/p' \
  "$blocking_source" >"$blocking_revoke"
sed -n '/^noncomputable def revokeSubtreeWords /,/^\/-- Accepted transitive revocation/p' \
  "$blocking_source" >"$blocking_subtree"

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
  'a raw-slot capability lookup in model-facing map dispatch'

require_literal "$ipc_source" '| send (handleWord : UInt64)' \
  'an opaque send-handle word'
require_literal "$ipc_source" '| receive (handleWord : UInt64)' \
  'an opaque receive-handle word'
require_literal "$ipc_dispatch" 'CapabilityHandle.resolveCurrent' \
  'generation-checked endpoint resolution'
require_literal "$ipc_dispatch" 'resolution.handle.slot' \
  'post-resolution internal-slot dispatch'
reject_pattern "$ipc_dispatch" 'Capability\.lookup|handleWord\.toNat' \
  'a raw-slot capability lookup in model-facing IPC dispatch'

require_literal "$blocking_source" 'def receiveOrBlockWord' \
  'an opaque blocking-receive boundary'
require_literal "$blocking_source" 'def sendWord' \
  'an opaque blocking-send boundary'
require_literal "$blocking_dispatch" 'CapabilityHandle.resolveCurrent' \
  'generation-checked blocking IPC resolution'
require_literal "$blocking_dispatch" 'resolution.handle.slot' \
  'post-resolution blocking IPC slot dispatch'
reject_pattern "$blocking_dispatch" 'Capability\.lookup|handleWord\.toNat' \
  'a raw-slot capability lookup in model-facing blocking IPC dispatch'
require_literal "$blocking_revoke" 'CapabilityHandle.revokeWords' \
  'generation-checked blocking IPC revocation'
reject_pattern "$blocking_revoke" 'Capability\.revoke[[:space:]]' \
  'a raw-slot capability revoke in the blocking IPC word boundary'
require_literal "$blocking_subtree" 'CapabilityHandle.revokeSubtreeWords' \
  'generation-checked blocking IPC subtree revocation'
reject_pattern "$blocking_subtree" 'Capability\.revokeSubtree' \
  'a raw-slot subtree revoke in the blocking IPC word boundary'

if (( failure != 0 )); then
  exit 1
fi

echo "Model-facing capability boundary source-policy checks passed"
