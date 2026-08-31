#!/usr/bin/env bash
set -euo pipefail

if [[ "${1:-}" == --version ]]; then
  echo "gcc (LeanOS controlled fixture) 13.3.0"
  exit 0
fi

echo "controlled compiler failure fixture" >&2
exit 86
