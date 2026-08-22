#!/usr/bin/env bash
# Unit tests for scripts/generate-invariants.py: the extractor must find
# theorems through the repository's declaration shapes (attributes, modifier
# keywords, names on the following line, nested namespaces) and must NOT count
# commented-out declarations or examples as theorems; verify must accept the
# committed INVARIANTS.md and reject mutated copies.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tool="$root/scripts/generate-invariants.py"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

fail() { echo "test-generate-invariants error: $*" >&2; exit 1; }

# --- extractor fixture -------------------------------------------------------
mkdir -p "$work/repo/LeanOS" "$work/repo/scripts"
cp "$tool" "$work/repo/scripts/generate-invariants.py"
cat >"$work/repo/LeanOS.lean" <<'EOF'
import LeanOS.Fixture
EOF
cat >"$work/repo/LeanOS/Fixture.lean" <<'EOF'
/-! Fixture module for the INVARIANTS extractor tests. -/

namespace LeanOS.Fixture

/-- Plain theorem with a docstring. -/
theorem plain_fact : 1 + 1 = 2 := rfl

@[simp] theorem attributed_fact : 2 + 0 = 2 := rfl

private theorem hidden_fact : 0 + 3 = 3 := rfl

set_option maxHeartbeats 400000 in
theorem
    name_on_next_line :
    4 = 4 := rfl

namespace Inner
theorem nested_fact : 5 = 5 := rfl
end Inner

section
theorem sectioned_fact : 6 = 6 := rfl
end

-- theorem commented_out : 7 = 7 := rfl
/- block comment:
theorem also_commented_out : 8 = 8 := rfl
-/
example : 9 = 9 := rfl

end LeanOS.Fixture
EOF

json="$("$work/repo/scripts/generate-invariants.py" extract)"
python3 - "$json" <<'EOF'
import json, sys
data = json.loads(sys.argv[1])
names = [t["display"] for t in data["files"]["LeanOS/Fixture.lean"]]
expected = ["plain_fact", "attributed_fact", "hidden_fact",
            "name_on_next_line", "Inner.nested_fact", "sectioned_fact"]
assert names == expected, f"extractor names {names} != {expected}"
assert data["total_theorems"] == 6, data["total_theorems"]
assert data["total_examples"] == 1, data["total_examples"]
docs = {t["display"]: t["docstring"] for t in data["files"]["LeanOS/Fixture.lean"]}
assert "docstring" in docs["plain_fact"].lower() or docs["plain_fact"], docs
EOF

# --- assemble + verify round trip on the fixture -----------------------------
mkdir -p "$work/sections"
cat >"$work/sections/LeanOS__Fixture.md" <<'EOF'
# Fixture facts

Small arithmetic facts used only to test the extractor.

- `plain_fact` — One plus one equals two.
- `attributed_fact` — Two plus zero equals two.
- `hidden_fact` — Zero plus three equals three.
- `name_on_next_line` — Four equals four.
- `Inner.nested_fact` — Five equals five.
- `sectioned_fact` — Six equals six.
EOF
"$work/repo/scripts/generate-invariants.py" assemble \
  --sections-dir "$work/sections" --output "$work/repo/INVARIANTS.md" \
  --generator test-model --date 2026-01-01 >/dev/null
"$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/repo/INVARIANTS.md" >/dev/null ||
  fail "verify rejected a freshly assembled fixture document"

# Dropping a bullet must fail verification.
grep -v 'hidden_fact' "$work/repo/INVARIANTS.md" >"$work/mutilated.md"
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/mutilated.md" >/dev/null 2>&1; then
  fail "verify accepted a document missing a theorem"
fi

# An invented bullet must fail verification.
sed 's/- `sectioned_fact`.*/&\n- `invented_fact` — Not proved anywhere./' \
  "$work/repo/INVARIANTS.md" >"$work/padded.md"
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/padded.md" >/dev/null 2>&1; then
  fail "verify accepted a document listing an unproved theorem"
fi

# A stale totals marker must fail verification.
sed 's/invariants:totals theorems=6/invariants:totals theorems=7/' \
  "$work/repo/INVARIANTS.md" >"$work/stale.md"
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/stale.md" >/dev/null 2>&1; then
  fail "verify accepted a stale totals marker"
fi

# Stale human-readable totals must fail independently of the marker.
sed 's/prove \*\*6 named theorems\*\*/prove **7 named theorems**/' \
  "$work/repo/INVARIANTS.md" >"$work/stale-prose.md"
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/stale-prose.md" >/dev/null 2>&1; then
  fail "verify accepted stale prose totals"
fi

# --- the committed document must match the real sources ----------------------
"$root/scripts/check-invariants.sh" >/dev/null

echo "test-generate-invariants: OK"
