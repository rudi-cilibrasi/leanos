#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
elf="${1:-$repo_root/build/boot/leanos.elf}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

run_fixture() {
  local name="$1" expected="$2"
  shift 2
  cp "$repo_root/boot/kernel.c" "$tmp/kernel.c"
  "$@" "$tmp/kernel.c"
  if LEANOS_KERNEL_SOURCE="$tmp/kernel.c" \
      "$repo_root/scripts/check-runtime-invalidation-policy.sh" "$elf" \
      >"$tmp/$name.log" 2>&1; then
    echo "error: runtime invalidation fixture $name unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: runtime invalidation fixture $name lacked diagnostic: $expected" >&2
    cat "$tmp/$name.log" >&2
    exit 1
  }
}

wrong_page() {
  sed -i 's/#define RUNTIME_MAPPING_PAGE 7u/#define RUNTIME_MAPPING_PAGE 8u/' "$1"
}

wrong_root() {
  sed -i \
    '/volatile uint64_t.*page_table_b.*RUNTIME_MAPPING_PAGE.*= 0/s/page_table_b/page_table_a/' \
    "$1"
}

omitted_invlpg() {
  sed -i '0,/invlpg (%0)/s//invlpg-omitted (%0)/' "$1"
}

forged_reply() {
  sed -i '0,/canonical_reply != LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED/s//canonical_reply != LEANOS_COMPOSITE_REPLY_UNMAPPED_PAGE_REJECTED/' "$1"
}

wrong_relation_space() {
  sed -i \
    's/if (space != 2 || page != RUNTIME_MAPPING_PAGE)/if (space != 1 || page != RUNTIME_MAPPING_PAGE)/' \
    "$1"
}

accept_unknown_state() {
  sed -i \
    '/static int checked_runtime_leaf(/,/^}/s/default:/case 99u:/' \
    "$1"
}

run_fixture wrong-page \
  'mutable-window target is not confined to page 7' wrong_page
run_fixture wrong-root \
  'PTE mutation is not confined to address space B/page 7' wrong_root
run_fixture omitted-invlpg \
  'active-root path does not contain exactly one INVLPG' omitted_invlpg
run_fixture forged-reply \
  'closed typed-reply checks drifted' forged_reply
run_fixture wrong-relation-space \
  'mutable-leaf exception is not confined to address space B/page 7' \
  wrong_relation_space
run_fixture accept-unknown-state \
  'unknown mutable-leaf states are not rejected' accept_unknown_state

echo "Runtime mapping invalidation negative fixtures passed"
