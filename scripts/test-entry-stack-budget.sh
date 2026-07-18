#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/usage.su" <<'EOF'
fixture.c:1:1:root	8	static
fixture.c:2:1:leaf	16	static
fixture.c:3:1:detached	8	static
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

printf 'one-byte-over\tkernel\t0\t1\tfixture_root\troot;leaf\n' >"$tmp/over.tsv"
run_rejected over 'over budget by 1 byte(s)'
printf 'indirect\tkernel\t0\t0\tfixture_root\troot;*handler\n' >"$tmp/indirect.tsv"
run_rejected indirect 'unresolved-indirect-edge=*handler'
printf 'recursive\tkernel\t0\t0\tfixture_root\troot;leaf;root\n' >"$tmp/recursive.tsv"
run_rejected recursive 'recursion=root'
printf 'unknown\tkernel\t0\t0\tfixture_root\troot;missing\n' >"$tmp/unknown.tsv"
run_rejected unknown 'missing-stack-usage=missing'
printf 'fixture.c:4:1:dynamic_leaf\t16\tdynamic,bounded\n' >>"$tmp/usage.su"
printf 'dynamic\tkernel\t0\t0\tfixture_root\troot;dynamic_leaf\n' >"$tmp/dynamic.tsv"
run_rejected dynamic 'function=dynamic_leaf stack-usage=dynamic,bounded'

printf 'ok\tkernel\t0\t0\tfixture_root\troot;leaf\n' >"$tmp/ok.tsv"
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

cat >"$tmp/fixture.S" <<'EOF'
.text
.globl fixture_root, root, leaf, detached, indirect_root
fixture_root: call root; ret
root: call leaf; ret
leaf: ret
detached: ret
indirect_root: call *%rax; ret
EOF
gcc -c "$tmp/fixture.S" -o "$tmp/fixture.o"
ld --build-id=none -o "$tmp/fixture.elf" -e fixture_root "$tmp/fixture.o"
LEANOS_STACK_USAGE_DIR="$tmp" LEANOS_ENTRY_STACK_MANIFEST="$tmp/ok.tsv" \
  LEANOS_ENTRY_STACK_USABLE_BYTES=184 \
  LEANOS_ENTRY_STACK_ELF_EDGES_OUTPUT="$tmp/edges.tsv" \
  ./scripts/check-entry-stack-budget.sh "$tmp/fixture.elf" >"$tmp/elf-ok.log"
grep -Fq $'fixture_root\troot' "$tmp/edges.tsv"
grep -Fq 'path=ok final-elf-root=fixture_root reviewed-functions=2' "$tmp/elf-ok.log"

run_rejected_elf() {
  local name="$1" diagnostic="$2"
  if LEANOS_STACK_USAGE_DIR="$tmp" LEANOS_ENTRY_STACK_MANIFEST="$tmp/$name.tsv" \
      LEANOS_ENTRY_STACK_USABLE_BYTES=184 ./scripts/check-entry-stack-budget.sh \
      "$tmp/fixture.elf" >"$tmp/$name-elf.log" 2>&1; then
    echo "error: final-ELF fixture '$name' unexpectedly passed" >&2; exit 1
  fi
  grep -Fq "$diagnostic" "$tmp/$name-elf.log" || {
    echo "error: final-ELF fixture '$name' lacked '$diagnostic'" >&2
    cat "$tmp/$name-elf.log" >&2; exit 1
  }
}
printf 'detached\tkernel\t0\t0\tfixture_root\troot;detached\n' >"$tmp/detached.tsv"
run_rejected_elf detached 'final-elf-unreachable-function=detached'
printf 'elf-indirect\tkernel\t0\t0\tindirect_root\troot\n' >"$tmp/elf-indirect.tsv"
run_rejected_elf elf-indirect 'final-elf-indirect-edge=indirect_root:'
echo 'entry-stack budget fixtures passed'
