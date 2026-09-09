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
for fixture in accepted wrong-stepping missing-smep unexpected-smap; do
  cpu='max,vendor=GenuineIntel,family=6,model=55,stepping=8,xsave=off,avx=off,smap=off'
  expected=65536
  case "$fixture" in
    wrong-stepping) cpu="${cpu/stepping=8/stepping=9}"; expected=6 ;;
    missing-smep) cpu+=',smep=off'; expected=9 ;;
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
  python3 - "$output/$fixture.log" "$expected" "$LEANOS_SERIAL_24_BOOT" \
      "$LEANOS_SERIAL_24_CPU" "$LEANOS_SERIAL_24_CONTROL" "$LEANOS_SERIAL_3_FINAL" <<'PY'
from pathlib import Path
import re
import sys
path, expected, boot, cpu, control, final = sys.argv[1:]
raw = Path(path).read_bytes()
assert raw.endswith(b'\n') and b'\r' not in raw
lines = raw.decode('ascii').splitlines()
assert lines[0] == boot + ' target=qotom-j1900-candidate phase=cpu-diagnostic platform-admitted=0 cpl3=0'
match = re.fullmatch(re.escape(cpu) + r' profile=j1900-cpu-v1 codec=1 width=22 words=([0-9,]+) selection=([0-9]+)', lines[1])
assert match and match[2] == expected
words = [int(word) for word in match[1].split(',')]
assert len(words) == 22 and all(word <= 0xffffffff for word in words)
assert words[:2] == [1, 31]
assert words[3:6] == [0x756e6547, 0x6c65746e, 0x49656e69]
if expected == '65536':
    assert len(lines) == 4
    assert words[6] == 0x30678
    assert lines[2] == control + ' profile=j1900-cpu-v1 codec=1 width=8 words=3328,0,0,0,0,0,0,0 readback=1'
    reason = 'qotom-platform-pending'
else:
    assert len(lines) == 3  # No RDMSR/readback record after CPU rejection.
    reason = 'j1900-cpu-profile'
assert lines[-1] == final + ' status=FAIL reason=' + reason
print(Path(path).stem + ': exact CPU diagnostic and terminal rejection verified')
PY
done
