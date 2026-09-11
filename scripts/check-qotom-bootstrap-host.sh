#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
python3 scripts/qotom-bootstrap-corpus.py
export LEANOS_HOSTED_BOUNDARY_ID=qotom-bootstrap
export LEANOS_QOTOM_BOOTSTRAP_REPLAY=build/qotom-bootstrap-corpus/replay.tsv
exec scripts/check-boot-handoff-host.sh "${1:-ordinary}"
