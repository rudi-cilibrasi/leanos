#!/usr/bin/env bash
# Refinement-ladder mutation check (issue #475). Every mutant in
# tests/fixtures/refinement-mutants.tsv must be rejected for its expected
# reason:
#   lean  — the export's Lean body, mutated and renamed, together with its
#           agreement theorems and their unchanged proofs, fails to elaborate;
#   c     — the emitted C, patched, fails the hosted oracle replay (and, for
#           an export of scripts/refinement-exports.tsv, the rung-3 drift
#           check);
#   drift — the emitted C, patched, fails the rung-3 drift check against the
#           AST its refinement theorem is about (issue #570; for exports
#           outside the oracle harness);
#   claim — a weakened claim statement fails the pinned contract
#           tests/RefinementStatements.lean.
# Needs a prior ordinary oracle replay (build/oracle, hosted sources).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
table="${LEANOS_REFINEMENT_MUTANT_TABLE:-tests/fixtures/refinement-mutants.tsv}"
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

# The Lean file holding the proved AST of a refined C function, if any.
refined_ast() {
  awk -F'\t' -v fn="$1" '$1 !~ /^#/ && $2 == fn { print $3 }' scripts/refinement-exports.tsv
}

# The generated C module of a refined C function.
refined_module() {
  awk -F'\t' -v fn="$1" '$1 !~ /^#/ && $2 == fn { print $1 }' scripts/refinement-exports.tsv
}

# The claim theorem of LeanOS.SecurityClaims a `claim` mutant weakens.
claim_theorem() {
  case "$1" in
    leanos_boot_transition) echo boot_transition_refinement ;;
    leanos_spawn_syscall) echo spawn_syscall_refinement ;;
    leanos_spawn_syscall_value) echo spawn_syscall_value_refinement ;;
    leanos_loader_source) echo loader_source_refinement ;;
    leanos_loader_decide) echo loader_decide_refinement ;;
    leanos_frame_copy_check) echo frame_copy_check_refinement ;;
    leanos_frame_port_check) echo frame_port_check_refinement ;;
    *) echo "error: no refinement claim for $1" >&2; exit 1 ;;
  esac
}

patch_export() {  # source export old new out: replace once inside the export
  python3 - "$@" <<'PY'
import re, sys
from pathlib import Path
source, export, old, new, out = sys.argv[1:6]
text = Path(source).read_text()
# The definition (parameters named `v_…`), not the forward declaration.
start = re.search(rf"^LEAN_EXPORT uint(?:64|8)_t {re.escape(export)}\(uint(?:64|8)_t v_",
                  text, re.M).start()
end = text.index("\nLEAN_EXPORT", start + 1)
body = text[start:end]
if old not in body:
    raise SystemExit(f"mutation anchor not found in {export}: {old!r}")
Path(out).write_text(text[:start] + body.replace(old, new, 1) + text[end:])
PY
}

drift_mutant() {
  local id="$1" export="$2" old="$3" new="$4"
  local module ast
  module="$(refined_module "$export")"; ast="$(refined_ast "$export")"
  [[ -n "$module" && -n "$ast" ]] || { echo "error: $export has no proved AST" >&2; exit 1; }
  if [[ ! -f "$tmp/generated-$module.c" ]]; then
    # The oracle replay's `lean --c` output when it has the module, else the
    # same generation here (build-image.sh emits build/boot/*.c this way).
    if [[ -f "$generated/$module.c" ]]; then
      cp "$generated/$module.c" "$tmp/generated-$module.c"
    else
      lake env lean --c="$tmp/generated-$module.c" "LeanOS/$module.lean"
    fi
    # The unmutated C must pass, so a mutant fails because of its mutation.
    python3 scripts/extract-generated-c.py --check "$tmp/generated-$module.c" "$export" "$ast" \
      >/dev/null
  fi
  patch_export "$tmp/generated-$module.c" "$export" "$old" "$new" "$tmp/$id.c"
  if python3 scripts/extract-generated-c.py --check "$tmp/$id.c" "$export" "$ast" \
      >"$tmp/$id.log" 2>&1; then
    echo "error: refinement mutant $id passed the rung-3 drift check" >&2; exit 1
  fi
}

c_mutant() {
  local id="$1" export="$2" old="$3" new="$4"
  local module; module="$(c_source "$export")"
  patch_export "$generated/$module.c" "$export" "$old" "$new" "$tmp/$module.c"
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
  local ast; ast="$(refined_ast "$export")"
  if [[ -n "$ast" ]] &&
      python3 scripts/extract-generated-c.py --check "$tmp/$module.c" "$export" "$ast" \
        >/dev/null 2>&1; then
    echo "error: refinement mutant $id passed the rung-3 drift check" >&2; exit 1
  fi
}

claim_fixture() {  # id export old new: write the weakened-claim fixture
  local id="$1" export="$2" old="$3" new="$4"
  local theorem; theorem="$(claim_theorem "$export")"
  python3 - "$theorem" "$old" "$new" "$tmp/$id.lean" <<'PY'
import re, sys
from pathlib import Path
theorem, old, new, out = sys.argv[1:5]
old = old.replace("\\n", "\n"); new = new.replace("\\n", "\n")
claims = Path("LeanOS/SecurityClaims.lean").read_text()
# The statement: from `theorem NAME` to the `:=` (or `:= by`) that ends its
# line.
match = re.search(rf"^theorem {theorem} (.*?):=(?: by)?[ ]*$", claims, re.S | re.M)
if not match:
    raise SystemExit(f"claim theorem not found: {theorem}")
statement = f"theorem {theorem} " + match.group(1).rstrip()
if old not in statement:
    raise SystemExit(f"mutation anchor not found in {theorem}: {old!r}")
weakened = statement.replace(old, new, 1).replace(
    f"theorem {theorem} ", f"theorem weakened_{theorem} ", 1)
contract = re.sub(rf"\bLeanOS\.SecurityClaims\.{theorem}\b",
    f"LeanOS.SecurityClaims.weakened_{theorem}",
    Path("tests/RefinementStatements.lean").read_text())
Path(out).write_text(contract.replace(
    "\n/--\ninfo:", "\nnamespace LeanOS.SecurityClaims\nopen LeanOS\n" + weakened +
    " := by\n  sorry\nend LeanOS.SecurityClaims\n\n/--\ninfo:", 1))
PY
}

claim_mutant() {
  claim_fixture "$@"
  if lake env lean "$tmp/$1.lean" >"$tmp/$1.log" 2>&1; then
    echo "error: refinement mutant $1 was accepted (claim contract)" >&2; exit 1
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
# Likewise every claim a `claim` mutant weakens: restated unchanged, its
# fixture must satisfy the pinned contract.
while IFS=$'\t' read -r id export kind _; do
  [[ -z "$id" || "$id" == \#* || "$kind" != claim ]] && continue
  theorem="$(claim_theorem "$export")"
  [[ -f "$tmp/identity-$theorem.lean" ]] && continue
  claim_fixture "identity-$theorem" "$export" "$theorem" "$theorem"
  if ! lake env lean "$tmp/identity-$theorem.lean" >"$tmp/identity-$theorem.log" 2>&1; then
    echo "error: unmutated claim fixture for $theorem fails the contract" >&2
    cat "$tmp/identity-$theorem.log" >&2; exit 1
  fi
done <"$table"
count=0
while IFS=$'\t' read -r id export kind old new expected; do
  [[ -z "$id" || "$id" == \#* ]] && continue
  case "$kind" in
    lean)
      if lean_mutant "$id" "$export" "$old" "$new"; then
        echo "error: refinement mutant $id was accepted (Lean)" >&2; exit 1
      fi ;;
    c) c_mutant "$id" "$export" "$old" "$new" ;;
    drift) drift_mutant "$id" "$export" "$old" "$new" ;;
    claim) claim_mutant "$id" "$export" "$old" "$new" ;;
    *) echo "error: unknown mutant kind $kind ($id)" >&2; exit 1 ;;
  esac
  grep -q "$expected" "$tmp/$id.log" || {
    echo "error: refinement mutant $id failed without '$expected'" >&2
    cat "$tmp/$id.log" >&2; exit 1
  }
  count=$((count + 1))
done <"$table"
echo "refinement ladder rejects all $count mutants"
