#!/usr/bin/env bash
set -euo pipefail
[[ "${1:-}" == --version ]] && { echo "QEMU fixture version 1"; exit 0; }
log=""; for arg in "$@"; do [[ "$arg" == file:* ]] && log="${arg#file:}"; done
[[ -n "$log" ]] || exit 2
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
success) printf '%s\n' 'LEANOS/1 BOOT target=x86_64-q35' 'LEANOS/1 TRANSITION state=0 command=1 result=1' 'LEANOS/1 TRANSITION state=0 command=7 result=0' 'LEANOS/1 FINAL status=PASS' > "$log"; exit 33;;
missing) : > "$log"; exit 33;;
partial) echo 'LEANOS/1 BOOT target=x86_64-q35' > "$log"; exit 33;;
guest-error) echo 'LEANOS/1 FINAL status=FAIL' > "$log"; exit 35;;
hang) sleep 10;;
*) exit 2;; esac
