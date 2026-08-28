#!/usr/bin/env bash
set -euo pipefail

log_dir="$1"
category="$2"
fixture="$3"
fixture_path="tests/negative/${fixture}.lean"
fixture_log="${log_dir}/${fixture}.log"

if lake env lean "$fixture_path" >"$fixture_log" 2>&1; then
  echo "error: ${category} fixture ${fixture} unexpectedly type-checked" >&2
  exit 1
fi

if ! grep -Fq "$fixture_path" "$fixture_log" ||
    ! grep -Fq 'error: Tactic `native_decide` evaluated that the proposition' \
      "$fixture_log" || ! grep -Fq 'is false' "$fixture_log"; then
  echo "error: ${category} fixture ${fixture} lacked its expected semantic diagnostic" >&2
  cat "$fixture_log" >&2
  exit 1
fi
