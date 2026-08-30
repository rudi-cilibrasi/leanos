#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fixture_root="$(mktemp -d)"
trap 'rm -rf "$fixture_root"' EXIT

mkdir -p "$fixture_root/LeanOS" "$fixture_root/docs/adr" "$fixture_root/scripts"
cp "$repo_root/scripts/check-native-decide-policy.py" "$fixture_root/scripts/"

write_policy() {
  cat >"$fixture_root/docs/adr/0001-phase-1-scope-threat-model-and-tcb.md" <<'EOF'
<!-- native-decide-policy:start -->
`native_decide` and `Lean.ofReduceBool` use the native evaluator, not kernel reduction.
The classification is `scripts/native-decide-modules.tsv`.
<!-- native-decide-policy:end -->
| `native_decide` / `Lean.ofReduceBool` native proof path | test | test | test |
EOF
}

write_policy
printf 'LeanOS/Example.lean\tbounded-model\n' >"$fixture_root/scripts/native-decide-modules.tsv"
cat >"$fixture_root/LeanOS/Example.lean" <<'EOF'
-- native_decide in a comment is not a use.
def diagnostic := "native_decide and Lean.ofReduceBool"
example : True := by native_decide
EOF

python3 "$fixture_root/scripts/check-native-decide-policy.py" --root "$fixture_root" \
  | grep -Fq 'total: 1 uses in 1 modules'

cat >"$fixture_root/LeanOS/Unclassified.lean" <<'EOF'
example : True := by native_decide
EOF
if python3 "$fixture_root/scripts/check-native-decide-policy.py" --root "$fixture_root" \
    >/dev/null 2>&1; then
  echo "error: unclassified native_decide module passed policy check" >&2
  exit 1
fi
rm "$fixture_root/LeanOS/Unclassified.lean"

printf '\n#check Lean.ofReduceBool\n' >>"$fixture_root/LeanOS/Example.lean"
if python3 "$fixture_root/scripts/check-native-decide-policy.py" --root "$fixture_root" \
    >/dev/null 2>&1; then
  echo "error: direct Lean.ofReduceBool use passed policy check" >&2
  exit 1
fi
sed -i '$d' "$fixture_root/LeanOS/Example.lean"

sed -i '/native-decide-policy:end/d' \
  "$fixture_root/docs/adr/0001-phase-1-scope-threat-model-and-tcb.md"
if python3 "$fixture_root/scripts/check-native-decide-policy.py" --root "$fixture_root" \
    >/dev/null 2>&1; then
  echo "error: missing native_decide policy marker passed policy check" >&2
  exit 1
fi

echo "native_decide policy checker regression tests passed"
