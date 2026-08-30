#!/usr/bin/env bash

leanos_harness_calls_export() {
  local harness="$1"
  local symbol="$2"

  sed '/^[[:space:]]*extern[[:space:]]/d' "$harness" |
    grep -E "(^|[^[:alnum:]_])${symbol}[[:space:]]*\\(" >/dev/null
}

leanos_harness_dispatches_generated_oracle_export() {
  local harness="$1"
  local symbol="$2"
  local oracle_source="$3"

  grep -F '#include "leanos/oracle-dispatch.h"' "$harness" >/dev/null &&
    sed '/^[[:space:]]*extern[[:space:]]/d' "$harness" |
      grep -E '(^|[^[:alnum:]_])leanos_oracle_dispatch[[:space:]]*\(' >/dev/null &&
    grep -E "adapter[[:space:]]+\"[^\"]+\"[[:space:]]+[0-9]+[[:space:]]+\"${symbol}\"[[:space:]]+[0-9]+" \
      "$oracle_source" >/dev/null
}
