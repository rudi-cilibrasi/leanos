#!/usr/bin/env bash
# Refinement-ladder mutation check (issue #475). Every mutant in
# tests/fixtures/refinement-mutants.tsv must be rejected for its expected
# reason:
#   lean  — the export's Lean body, mutated and renamed, together with its
#           agreement theorems and their unchanged proofs, fails to elaborate;
#   c     — the emitted C, patched, fails the hosted oracle replay (and, for
#           leanos_boot_transition, the rung-3 drift check);
#   claim — a weakened claim statement fails the pinned contract
#           tests/RefinementStatements.lean.
# Needs a prior ordinary oracle replay (build/oracle, hosted sources).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
table=tests/fixtures/refinement-mutants.tsv
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
generated=build/hosted-generated-sources/oracle
prefix="$(lake env lean --print-prefix)"

lean_source() {  # export -> "file|first-def-line-regex|last-theorem-name|name"
  case "$1" in
    leanos_boot_transition)
      echo "LeanOS/KernelTransition.lean|^@\[export leanos_boot_transition\]|bootTransition_agrees|bootTransition" ;;
    leanos_blocking_ipc_event)
      echo "LeanOS/BlockingIPC.lean|^@\[export leanos_blocking_ipc_event\]|blockingIpcEvent_accepts_only_edges|blockingIpcEvent" ;;
    *) echo "error: no Lean source for $1" >&2; exit 1 ;;
  esac
}

c_source() {
  case "$1" in
    leanos_boot_transition) echo KernelTransition ;;
    leanos_blocking_ipc_event) echo BlockingIPC ;;
    *) echo "error: no generated module for $1" >&2; exit 1 ;;
  esac
}

lean_mutant() {
  local id="$1" export="$2" old="$3" new="$4"
  IFS='|' read -r file start last name <<<"$(lean_source "$export")"
  local module="${file#LeanOS/}"; module="LeanOS.${module%.lean}"
  python3 - "$file" "$start" "$last" "$name" "$old" "$new" "$module" "$tmp/$id.lean" <<'PY'
import re, sys
from pathlib import Path
file, start, last, name, old, new, module, out = sys.argv[1:9]
old = old.replace("\\n", "\n"); new = new.replace("\\n", "\n")
text = Path(file).read_text()
lines = text.splitlines(keepends=True)
begin = next(i for i, l in enumerate(lines) if re.match(start, l))
# The definition through the last named theorem and its proof (up to the
# next blank line after that theorem).
theorem = next(i for i, l in enumerate(lines) if l.startswith(f"theorem {last}"))
end = next((i for i in range(theorem, len(lines)) if lines[i].strip() == ""), len(lines))
block = "".join(lines[begin + 1:end])  # drop the @[export] attribute
def_end = block.index("\ntheorem") if "\ntheorem" in block else block.index("\n/--")
definition, rest = block[:def_end], block[def_end:]
if old not in definition:
    raise SystemExit(f"mutation anchor not found in {name}: {old!r}")
definition = definition.replace(old, new, 1)
mutant = re.sub(rf"\b{name}", f"mutant{name[0].upper()}{name[1:]}", definition + rest)
namespace = re.search(r"^namespace (\S+)", text, re.M).group(1)
# Private one-line definitions the block uses are invisible from another
# file; copy them into the fixture.
privates = "".join(
    m.group(0) + "\n" for m in re.finditer(r"^private def (\w+) .*$", text, re.M)
    if re.search(rf"\b{m.group(1)}\b", mutant))
Path(out).write_text(f"import {module}\n\nnamespace {namespace}\n\n{privates}{mutant}\nend {namespace}\n")
PY
  # Succeeds exactly when the fixture elaborates.
  lake env lean "$tmp/$id.lean" >"$tmp/$id.log" 2>&1
}

c_mutant() {
  local id="$1" export="$2" old="$3" new="$4"
  local module; module="$(c_source "$export")"
  python3 - "$generated/$module.c" "$export" "$old" "$new" "$tmp/$module.c" <<'PY'
import sys
from pathlib import Path
source, export, old, new, out = sys.argv[1:6]
text = Path(source).read_text()
start = text.index(f"LEAN_EXPORT uint64_t {export}(uint64_t v_")
end = text.index("\nLEAN_EXPORT", start + 1)
body = text[start:end]
if old not in body:
    raise SystemExit(f"mutation anchor not found in {export}: {old!r}")
Path(out).write_text(text[:start] + body.replace(old, new, 1) + text[end:])
PY
  local objects=()
  for object in build/oracle/*.o; do
    case "$(basename "$object")" in
      host*.o|boundary-coverage.o|"$module.o") ;;
      *) objects+=("$object") ;;
    esac
  done
  cc -std=c11 -I"$prefix/include" -Ibuild/oracle -ffunction-sections -fdata-sections \
    -finstrument-functions -c "$tmp/$module.c" -o "$tmp/$module.o"
  cc -Wl,--gc-sections -ffunction-sections -fdata-sections -finstrument-functions \
    build/oracle/host.o build/oracle/boundary-coverage.o "${objects[@]}" "$tmp/$module.o" \
    -o "$tmp/host-$id"
  if LEANOS_BOUNDARY_COVERAGE_FILE="$tmp/coverage-$id" "$tmp/host-$id" \
      >"$tmp/$id.log" 2>&1; then
    echo "error: refinement mutant $id passed the hosted oracle" >&2; exit 1
  fi
  if [[ "$export" == leanos_boot_transition ]] &&
      python3 scripts/extract-generated-c.py --check "$tmp/$module.c" "$export" \
        LeanOS/Refinement/BootTransitionC.lean >/dev/null 2>&1; then
    echo "error: refinement mutant $id passed the rung-3 drift check" >&2; exit 1
  fi
}

claim_mutant() {
  local id="$1" old="$2" new="$3"
  python3 - "$old" "$new" "$tmp/$id.lean" <<'PY'
import sys
from pathlib import Path
old, new, out = sys.argv[1:4]
old = old.replace("\\n", "\n"); new = new.replace("\\n", "\n")
claims = Path("LeanOS/SecurityClaims.lean").read_text()
start = claims.index("theorem boot_transition_refinement")
end = claims.index("\n\n", start)
statement = claims[start:end]
if old not in statement:
    raise SystemExit(f"mutation anchor not found in boot_transition_refinement: {old!r}")
weakened = statement.replace(old, new, 1).replace(
    "theorem boot_transition_refinement", "theorem weakened_boot_transition_refinement")
contract = Path("tests/RefinementStatements.lean").read_text().replace(
    "LeanOS.SecurityClaims.boot_transition_refinement",
    "LeanOS.SecurityClaims.weakened_boot_transition_refinement")
Path(out).write_text(contract.replace(
    "\n/--\ninfo:", "\nnamespace LeanOS.SecurityClaims\nopen LeanOS\n" + weakened +
    " := by\n  intro _\n  sorry\nend LeanOS.SecurityClaims\n\n/--\ninfo:", 1))
PY
  if lake env lean "$tmp/$id.lean" >"$tmp/$id.log" 2>&1; then
    echo "error: refinement mutant $id was accepted (claim contract)" >&2; exit 1
  fi
}

lake env lean tests/RefinementStatements.lean >/dev/null
# The unmutated fixture of each export must elaborate, so every Lean mutant
# fails because of its mutation and not because of the fixture generator.
for export in leanos_boot_transition leanos_blocking_ipc_event; do
  IFS='|' read -r _ _ _ name <<<"$(lean_source "$export")"
  if ! lean_mutant "identity-$export" "$export" "$name" "$name"; then
    echo "error: unmutated fixture for $export does not elaborate" >&2
    cat "$tmp/identity-$export.log" >&2; exit 1
  fi
done
count=0
while IFS=$'\t' read -r id export kind old new expected; do
  [[ -z "$id" || "$id" == \#* ]] && continue
  case "$kind" in
    lean)
      if lean_mutant "$id" "$export" "$old" "$new"; then
        echo "error: refinement mutant $id was accepted (Lean)" >&2; exit 1
      fi ;;
    c) c_mutant "$id" "$export" "$old" "$new" ;;
    claim) claim_mutant "$id" "$old" "$new" ;;
    *) echo "error: unknown mutant kind $kind ($id)" >&2; exit 1 ;;
  esac
  grep -q "$expected" "$tmp/$id.log" || {
    echo "error: refinement mutant $id failed without '$expected'" >&2
    cat "$tmp/$id.log" >&2; exit 1
  }
  count=$((count + 1))
done <"$table"
echo "refinement ladder rejects all $count mutants"
