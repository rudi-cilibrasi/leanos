#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

printf 'adapter-id\tKernelTransition\t0\tleanos_boot_transition\t2\n0\tknown\tKernelTransition\t0,0\t1\n' |
  awk -f "$root/scripts/render-oracle-header.awk" > "$tmp/known.h"
grep -Fq '{0,2,{0ULL,0ULL' "$tmp/known.h"

if printf 'adapter-id\tKernelTransition\t0\tleanos_boot_transition\t2\n0\tunknown\tTypo.adapter\t0\t0\n' |
    awk -f "$root/scripts/render-oracle-header.awk" > /dev/null 2> "$tmp/error"; then
  echo "error: unknown oracle adapter was accepted" >&2
  exit 1
fi
grep -Fxq 'error: unknown generated oracle adapter: Typo.adapter' "$tmp/error"
echo "Generated oracle adapter vocabulary rejects unknown names"
