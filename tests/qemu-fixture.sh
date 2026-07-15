#!/usr/bin/env bash
set -euo pipefail
[[ "${1:-}" == --version ]] && { echo "QEMU fixture version 1"; exit 0; }
log=""; for arg in "$@"; do [[ "$arg" == file:* ]] && log="${arg#file:}"; done
[[ -n "$log" ]] || exit 2
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
success) export log; sed -n '/^printf/,/expected"$/p' scripts/run-image.sh | sed '$s/ > "\$expected"/ > "\$log"/' | bash; exit 33;;
skipped-user) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 SYSCALL kind=forged result=rejected' 'LEANOS/2 FAULT vector=14 class=user-supervisor-access contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
forged-result) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 USER cpl=3' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 SYSCALL kind=forged result=accepted' 'LEANOS/2 FAULT vector=14 class=user-supervisor-access contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
reordered) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 USER cpl=3' 'LEANOS/2 SYSCALL kind=forged result=rejected' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 FAULT vector=14 class=user-supervisor-access contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
wrong-fault) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 USER cpl=3' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 SYSCALL kind=forged result=rejected' 'LEANOS/2 FAULT vector=13 class=general-protection contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
missing) : > "$log"; exit 33;;
partial) echo 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' > "$log"; exit 33;;
guest-error) echo 'LEANOS/2 FINAL status=FAIL' > "$log"; exit 35;;
hang) sleep 10;;
*) exit 2;; esac
