#!/usr/bin/env bash
# Device-program gate (LeanOS/Wifi, LeanOS/Usb, hardware/wifi/wifi-exec.h):
# the generator admits every firmware-free program under its target's
# confinement policy (LeanOS/DeviceProgramConfinement.lean), the C executor
# builds warning-free, and it agrees with LeanOS/Wifi/Sim.lean on the
# computation-only cross-check program.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
out=build/ci/device-programs
rm -rf "$out"
mkdir -p "$out"

lake build leanos-wifi-gen leanos-wifi-xcheck
for program in probe sprom tables kbd; do
  .lake/build/bin/leanos-wifi-gen "$program" "$out/$program.bin" >/dev/null
  # Version-3 header: the image carries its checked policy.
  version="$(od -An -tu4 -j4 -N4 "$out/$program.bin" | tr -d ' ')"
  if [[ "$version" != 3 ]]; then
    echo "error: $program image is version $version, expected 3 (policy header)" >&2
    exit 1
  fi
done

cc -std=c11 -Wall -Wextra -Werror -O2 -o "$out/host-runner" hardware/wifi/host-runner.c
.lake/build/bin/leanos-wifi-xcheck "$out/xcheck.bin" >"$out/sim.txt"
"$out/host-runner" "$out/xcheck.bin" >"$out/c.txt"
python3 - "$out/sim.txt" "$out/c.txt" <<'PY'
import sys
sim = [l.split() for l in open(sys.argv[1]) if l.startswith('WIFI ')]
c = [l.split() for l in open(sys.argv[2]) if l.startswith('WIFI ')]
sim = [(int(t, 16), int(v)) for _, t, v in sim]
c = [(int(t, 16), int(v, 16)) for _, t, v in c]
if not sim or sim != c:
    sys.exit(f'error: simulator and C executor transcripts differ ({len(sim)} vs {len(c)} records)')
if 'SIM-END LeanOS.Wifi.Sim.Status.halt' not in open(sys.argv[1]).read():
    sys.exit('error: simulator did not halt')
if 'WIFI-END status=0 ' not in open(sys.argv[2]).read():
    sys.exit('error: C executor did not halt')
print(f'device programs: admitted, {len(sim)} cross-check records agree')
PY
