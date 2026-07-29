#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
elf="${1:-$root/build/boot/leanos-frame-budget.elf}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

run_fixture() {
  local name="$1" expected="$2"
  shift 2
  cp "$root/boot/kernel.c" "$tmp/kernel.c"
  "$@" "$tmp/kernel.c"
  if LEANOS_KERNEL_SOURCE="$tmp/kernel.c" \
      "$root/scripts/check-frame-budget-machine.sh" "$elf" \
      >"$tmp/$name.log" 2>&1; then
    echo "error: frame-budget invalidation fixture $name unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$tmp/$name.log" || {
    echo "error: frame-budget invalidation fixture $name lacked diagnostic: $expected" >&2
    sed -n '1,160p' "$tmp/$name.log" >&2
    exit 1
  }
}

omit_effect_check() {
  sed -i \
    '/effect_token != LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN ||/d' "$1"
}

omit_flush() {
  sed -i \
    '/static void frame_budget_retire_mapping(/,/^}/s/"r"((uint64_t)page_map_level_4_b)/"r"((uint64_t)page_map_level_4_a)/' \
    "$1"
}

publish_before_flush() {
  sed -i \
    '/static void frame_budget_retire_mapping(/,/^}/ {
      /((volatile uint64_t \*)page_table)\[page\] = 0;/i\
    frame_budget_publication_live = 0;
      /frame_budget_publication_live = 0;/{$!{x;d;x;}}
    }' "$1"
}

omit_scrub_guard() {
  sed -i \
    '/if (frame_budget_retirement_completion !=$/,+2d' "$1"
}

run_fixture omitted-effect \
  'frame-budget retirement lacks the generated exact-effect check' \
  omit_effect_check
run_fixture wrong-flush-root \
  'frame-budget retirement lacks one exact CR3 reload' omit_flush
run_fixture early-publication \
  'frame-budget retirement order is not PTE-store, CR3-flush, acknowledge, publish' \
  publish_before_flush
run_fixture omitted-reuse-guard \
  'frame-budget scrub/reuse is not guarded by invalidation completion' \
  omit_scrub_guard

echo "Frame-budget invalidation source/final-ELF negative fixtures passed"
