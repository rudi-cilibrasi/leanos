#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/usage.su" <<'EOF'
fixture.c:1:1:root	8	static
fixture.c:2:1:leaf	16	static
EOF
run_rejected() {
  local name="$1" diagnostic="$2"
  if LEANOS_STACK_USAGE_DIR="$tmp" LEANOS_ENTRY_STACK_MANIFEST="$tmp/$name.tsv" \
      LEANOS_ENTRY_STACK_USABLE_BYTES=184 ./scripts/check-entry-stack-budget.sh \
      >"$tmp/$name.log" 2>&1; then
    echo "error: entry-stack fixture '$name' unexpectedly passed" >&2; exit 1
  fi
  grep -Fq "$diagnostic" "$tmp/$name.log" || {
    echo "error: entry-stack fixture '$name' lacked '$diagnostic'" >&2
    cat "$tmp/$name.log" >&2; exit 1
  }
}

printf 'one-byte-over\tkernel\t0\t1\troot;leaf\n' >"$tmp/over.tsv"
run_rejected over 'over budget by 1 byte(s)'
printf 'indirect\tkernel\t0\t0\troot;*handler\n' >"$tmp/indirect.tsv"
run_rejected indirect 'unresolved-indirect-edge=*handler'
printf 'recursive\tkernel\t0\t0\troot;leaf;root\n' >"$tmp/recursive.tsv"
run_rejected recursive 'recursion=root'
printf 'unknown\tkernel\t0\t0\troot;missing\n' >"$tmp/unknown.tsv"
run_rejected unknown 'missing-stack-usage=missing'
printf 'fixture.c:3:1:dynamic_leaf\t16\tdynamic,bounded\n' >>"$tmp/usage.su"
printf 'dynamic\tkernel\t0\t0\troot;dynamic_leaf\n' >"$tmp/dynamic.tsv"
run_rejected dynamic 'function=dynamic_leaf stack-usage=dynamic,bounded'

printf 'ok\tkernel\t0\t0\troot;leaf\n' >"$tmp/ok.tsv"
LEANOS_STACK_USAGE_DIR="$tmp" LEANOS_ENTRY_STACK_MANIFEST="$tmp/ok.tsv" \
  LEANOS_ENTRY_STACK_USABLE_BYTES=184 ./scripts/check-entry-stack-budget.sh >"$tmp/ok.log"
grep -Fq 'path=ok prefix=160 compiler=24 safety=0 total=184 usable=184 margin=0' "$tmp/ok.log"

awk 'BEGIN { inside = 0; changed = 0 }
  /^[.]macro SAVE$/ { inside = 1 }
  inside && !changed && /push %rax/ { sub(/push %rax/, "nop"); changed = 1 }
  { print }
  inside && /^[.]endm$/ { inside = 0 }' boot/boot.S >"$tmp/changed-save.S"
if LEANOS_STACK_USAGE_DIR="$tmp" LEANOS_ENTRY_STACK_MANIFEST="$tmp/ok.tsv" \
    LEANOS_ENTRY_ASSEMBLY_SOURCE="$tmp/changed-save.S" \
    LEANOS_ENTRY_STACK_USABLE_BYTES=184 ./scripts/check-entry-stack-budget.sh \
    >"$tmp/changed-save.log" 2>&1; then
  echo "error: changed assembly save-count fixture unexpectedly passed" >&2; exit 1
fi
grep -Fq 'assembly-save-register-count=14 expected=15' "$tmp/changed-save.log"
echo 'entry-stack budget fixtures passed'
