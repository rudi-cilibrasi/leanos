#!/usr/bin/env bash
# The #470 drift check must accept the emitted leanos_boot_transition and
# reject emitted C that changed, or that leaves the proved C subset.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
generated="${1:-build/boot/KernelTransition.c}"
proof=LeanOS/Refinement/BootTransitionC.lean
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 scripts/extract-generated-c.py --check "$generated" leanos_boot_transition "$proof" >/dev/null
reject() {
  local name="$1" old="$2" new="$3"
  python3 - "$generated" "$tmp/$name.c" "$old" "$new" <<'PY'
import sys
from pathlib import Path
source, target, old, new = sys.argv[1:5]
text = Path(source).read_text()
start = text.index("LEAN_EXPORT uint64_t leanos_boot_transition(uint64_t v_")
end = text.index("\nLEAN_EXPORT", start + 1)
body = text[start:end]
if old not in body:
    raise SystemExit(f"mutation anchor missing: {old}")
Path(target).write_text(text[:start] + body.replace(old, new, 1) + text[end:])
PY
  if python3 scripts/extract-generated-c.py --check "$tmp/$name.c" \
      leanos_boot_transition "$proof" >/dev/null 2>&1; then
    echo "error: drift check accepted mutated C ($name)" >&2
    exit 1
  fi
}
# A changed constant, comparison operand, and an out-of-subset construct.
reject accept-word "= 1ULL;
return" "= 2ULL;
return"
reject state-word "= 0ULL;" "= 5ULL;"
reject unsupported "lean_uint64_dec_eq(v_state" "lean_uint64_dec_lt(v_state"
echo "generated-C drift check accepts the proved AST and rejects 3 mutations"
