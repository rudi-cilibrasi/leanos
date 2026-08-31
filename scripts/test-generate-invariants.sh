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
"$work/repo/scripts/generate-invariants.py" identities >/dev/null
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
"$work/repo/scripts/generate-invariants.py" decompose >/dev/null
rendered="$work/rendered.md"
"$work/repo/scripts/generate-invariants.py" render --output "$rendered" >/dev/null
cmp -s "$work/repo/INVARIANTS.md" "$rendered" ||
  fail "checked-in sections did not reproduce the document byte-for-byte"
"$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/repo/INVARIANTS.md" >/dev/null ||
  fail "verify rejected a freshly assembled fixture document"

# Declaration order is not theorem identity. Reordering source declarations
# must not rewrite or invalidate the human summaries in the rendered index.
cp "$work/repo/LeanOS/Fixture.lean" "$work/Fixture.lean.orig"
python3 - "$work/repo/LeanOS/Fixture.lean" <<'EOF'
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text()
old = """theorem plain_fact : 1 + 1 = 2 := rfl

@[simp] theorem attributed_fact : 2 + 0 = 2 := rfl"""
new = """@[simp] theorem attributed_fact : 2 + 0 = 2 := rfl

theorem plain_fact : 1 + 1 = 2 := rfl"""
assert old in text
path.write_text(text.replace(old, new))
EOF
"$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/repo/INVARIANTS.md" >/dev/null ||
  fail "verify rejected an order-only source refactor"
mv "$work/Fixture.lean.orig" "$work/repo/LeanOS/Fixture.lean"

# Structured identities are the mechanical source/module/name record. A stale
# identity must fail even when the rendered prose remains complete.
python3 - "$work/repo/INVARIANTS.identities.json" <<'EOF'
from pathlib import Path
import json, sys

path = Path(sys.argv[1])
data = json.loads(path.read_text())
data["identities"][0]["qualified"] = "LeanOS.Fixture.stale_fact"
path.write_text(json.dumps(data, indent=2) + "\n")
EOF
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/repo/INVARIANTS.md" >/dev/null 2>&1; then
  fail "verify accepted a stale structured theorem identity"
fi
"$work/repo/scripts/generate-invariants.py" identities >/dev/null

# A same-module theorem rename carries its existing human summary and refreshes
# the mechanical identity index without an API key.
sed -i 's/theorem plain_fact/theorem renamed_plain_fact/' \
  "$work/repo/LeanOS/Fixture.lean"
"$work/repo/scripts/generate-invariants.py" rename \
  --old LeanOS.Fixture.plain_fact \
  --new LeanOS.Fixture.renamed_plain_fact \
  --document "$work/repo/INVARIANTS.md" >/dev/null
grep -q '^\- `renamed_plain_fact` — One plus one equals two\.$' \
  "$work/repo/INVARIANTS.md" || fail "rename did not preserve summary"
"$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/repo/INVARIANTS.md" >/dev/null ||
  fail "verify rejected deterministic theorem rename"
sed -i 's/theorem renamed_plain_fact/theorem plain_fact/' \
  "$work/repo/LeanOS/Fixture.lean"
sed -i 's/`renamed_plain_fact`/`plain_fact`/' "$work/repo/INVARIANTS.md"
"$work/repo/scripts/generate-invariants.py" identities >/dev/null

# A cross-module move relocates the existing summary into the destination
# section and refreshes identities without external generation.
cat >"$work/repo/LeanOS/Moved.lean" <<'EOF'
/-! Destination fixture module. -/

namespace LeanOS.Moved
theorem destination_fact : 10 = 10 := rfl
end LeanOS.Moved
EOF
sed -i '1a import LeanOS.Moved' "$work/repo/LeanOS.lean"
mkdir -p "$work/move-sections"
cp "$work/sections/LeanOS__Fixture.md" "$work/move-sections/LeanOS__Fixture.md"
cat >"$work/move-sections/LeanOS__Moved.md" <<'EOF'
# Moved facts

Facts in the destination fixture module.

- `destination_fact` — Ten equals ten.
EOF
"$work/repo/scripts/generate-invariants.py" assemble \
  --sections-dir "$work/move-sections" --output "$work/repo/INVARIANTS.md" \
  --generator test-model --date 2026-01-01 >/dev/null
"$work/repo/scripts/generate-invariants.py" decompose >/dev/null
"$work/repo/scripts/generate-invariants.py" identities >/dev/null
sed -i '/theorem sectioned_fact/d' "$work/repo/LeanOS/Fixture.lean"
sed -i '/theorem destination_fact/a theorem sectioned_fact : 6 = 6 := rfl' \
  "$work/repo/LeanOS/Moved.lean"
"$work/repo/scripts/generate-invariants.py" move \
  --old LeanOS.Fixture.sectioned_fact \
  --new LeanOS.Moved.sectioned_fact \
  --document "$work/repo/INVARIANTS.md" >/dev/null
python3 - "$work/repo/INVARIANTS.md" <<'EOF'
from pathlib import Path
import sys

text = Path(sys.argv[1]).read_text()
fixture, moved = text.split("## Moved facts", 1)
assert "`sectioned_fact` — Six equals six." not in fixture
assert "`sectioned_fact` — Six equals six." in moved
EOF
"$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/repo/INVARIANTS.md" >/dev/null ||
  fail "verify rejected deterministic cross-module theorem move"

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

# Repeating a real theorem is not set completeness: every identity must occur
# exactly once.
sed 's/- `sectioned_fact`.*/&\n- `sectioned_fact` — Duplicate summary./' \
  "$work/repo/INVARIANTS.md" >"$work/duplicated.md"
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/duplicated.md" >/dev/null 2>&1; then
  fail "verify accepted a duplicate theorem identity"
fi

# A stale totals marker must fail verification.
sed 's/invariants:totals theorems=7/invariants:totals theorems=8/' \
  "$work/repo/INVARIANTS.md" >"$work/stale.md"
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/stale.md" >/dev/null 2>&1; then
  fail "verify accepted a stale totals marker"
fi

# Stale human-readable totals must fail independently of the marker.
sed 's/prove \*\*7 named theorems\*\*/prove **8 named theorems**/' \
  "$work/repo/INVARIANTS.md" >"$work/stale-prose.md"
if "$work/repo/scripts/generate-invariants.py" verify \
  --document "$work/stale-prose.md" >/dev/null 2>&1; then
  fail "verify accepted stale prose totals"
fi

# --- the committed document must match the real sources ----------------------
"$root/scripts/check-invariants.sh" >/dev/null

echo "test-generate-invariants: OK"
