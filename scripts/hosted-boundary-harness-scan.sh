#!/usr/bin/env bash

leanos_harness_calls_export() {
  local harness="$1"
  local symbol="$2"

  sed '/^[[:space:]]*extern[[:space:]]/d' "$harness" |
    grep -E "(^|[^[:alnum:]_])${symbol}[[:space:]]*\\(" >/dev/null
}
