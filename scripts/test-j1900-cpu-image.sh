#!/usr/bin/env bash
# Diagnostic CPU fixtures only: these do not emulate the Qotom platform.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
image="${1:?usage: test-j1900-cpu-image.sh ISO [output-directory]}"
output="${2:-build/j1900-cpu-image}"
mkdir -p "$output"
export LEANOS_QEMU_ACCELERATOR=tcg
source scripts/q35-platform.sh
source build/boot/serial-protocol.sh
./scripts/check-j1900-cpu-host.sh ordinary > "$output/native-replay-build.log" 2>&1
for fixture in accepted wrong-stepping missing-smep unexpected-smap missing-structured-leaf; do
  cpu='max,vendor=GenuineIntel,family=6,model=55,stepping=8,xsave=off,avx=off,smap=off'
  expected=65536
  case "$fixture" in
    wrong-stepping) cpu="${cpu/stepping=8/stepping=9}"; expected=6 ;;
    missing-smep) cpu+=',smep=off'; expected=9 ;;
    missing-structured-leaf) cpu+=',level=6'; expected=2 ;;
    unexpected-smap) cpu="${cpu/smap=off/smap=on}"; expected=11 ;;
  esac
  command=()
  leanos_q35_command command qemu-system-x86_64 128 "$output/$fixture.log" "$image"
  # Mutate the CPU after validating the common machine/device construction.
  # These fixtures are never accepted as canonical q35 or physical evidence.
  for ((i=0; i<${#command[@]}; i++)); do
    if [[ "${command[$i]}" == -cpu ]]; then command[$((i+1))]="$cpu"; fi
  done
  set +e
  timeout --signal=TERM --kill-after=2s 15s "${command[@]}" > "$output/$fixture.stderr" 2>&1
  result=$?
  set -e
  [[ "$result" == 35 ]] || { echo "$fixture: unexpected QEMU status $result" >&2; exit 1; }
  python3 scripts/check-j1900-diagnostic.py "$output/$fixture.log" \
    > "$output/$fixture.replay.json"
  python3 - "$output/$fixture.replay.json" "$expected" <<'PY'
import json
from pathlib import Path
import sys
result = json.loads(Path(sys.argv[1]).read_text())
assert result['cpu_selection'] == int(sys.argv[2])
if int(sys.argv[2]) == 2:
    assert result['cpu_words'][1] == 27
    assert result['cpu_words'][2] == 6
    assert result['cpu_words'][10:14] == [0, 0, 0, 0]
print(Path(sys.argv[1]).stem + ': generated CPU/MSR replay and terminal verified')
PY
done
