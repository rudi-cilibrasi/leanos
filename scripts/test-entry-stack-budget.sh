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
      LEANOS_ENTRY_STACK_USABLE_BYTES=32 ./scripts/check-entry-stack-budget.sh \
      >"$tmp/$name.log" 2>&1; then
    echo "error: entry-stack fixture '$name' unexpectedly passed" >&2; exit 1
  fi
  grep -Fq "$diagnostic" "$tmp/$name.log" || {
    echo "error: entry-stack fixture '$name' lacked '$diagnostic'" >&2
    cat "$tmp/$name.log" >&2; exit 1
  }
}

printf 'one-byte-over\t9\t0\troot;leaf\n' >"$tmp/over.tsv"
run_rejected over 'over budget by 1 byte(s)'
printf 'indirect\t0\t0\troot;*handler\n' >"$tmp/indirect.tsv"
run_rejected indirect 'unresolved-indirect-edge=*handler'
printf 'recursive\t0\t0\troot;leaf;root\n' >"$tmp/recursive.tsv"
run_rejected recursive 'recursion=root'
printf 'unknown\t0\t0\troot;missing\n' >"$tmp/unknown.tsv"
run_rejected unknown 'missing-stack-usage=missing'
printf 'fixture.c:3:1:dynamic_leaf\t16\tdynamic,bounded\n' >>"$tmp/usage.su"
printf 'dynamic\t0\t0\troot;dynamic_leaf\n' >"$tmp/dynamic.tsv"
run_rejected dynamic 'function=dynamic_leaf stack-usage=dynamic,bounded'

printf 'ok\t8\t0\troot;leaf\n' >"$tmp/ok.tsv"
LEANOS_STACK_USAGE_DIR="$tmp" LEANOS_ENTRY_STACK_MANIFEST="$tmp/ok.tsv" \
  LEANOS_ENTRY_STACK_USABLE_BYTES=32 ./scripts/check-entry-stack-budget.sh >"$tmp/ok.log"
grep -Fq 'path=ok prefix=8 compiler=24 safety=0 total=32 usable=32 margin=0' "$tmp/ok.log"
echo 'entry-stack budget fixtures passed'
