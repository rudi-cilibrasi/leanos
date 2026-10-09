#!/usr/bin/env bash
# Device-program gate (LeanOS/Wifi, LeanOS/Usb, hardware/wifi/wifi-exec.h):
# the generator admits every firmware-free program under its target's
# confinement policy (LeanOS/DeviceProgramConfinement.lean), the C executor
# builds warning-free, and it agrees with LeanOS/Wifi/Sim.lean on the
# computation-only cross-check program and on random programs (differential
# fuzzing, issue #451). The fuzzer's power is itself checked: every mutant of
# wifi-exec.h in tests/fixtures/wifi-exec-mutants.txt must be caught.
# The generated executor (issue #494: the compiled LeanOS.Wifi.Exec.step,
# proved equal to Sim.step) runs the same corpus and must agree with both
# (scripts/check-generated-executor-host.sh), which also checks its
# freestanding boot shape.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
out=build/ci/device-programs
rm -rf "$out"
mkdir -p "$out"

lake build leanos-wifi-gen leanos-wifi-xcheck leanos-wifi-fuzz
for program in probe sprom tables kbd ahci-identify rtl8168-arp; do
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

# Differential fuzzing: simulator vs C executor on the same random images.
fuzz_count="${LEANOS_WIFI_FUZZ_COUNT:-3000}"
fuzz_seed="${LEANOS_WIFI_FUZZ_SEED:-451}"
.lake/build/bin/leanos-wifi-fuzz "$out/fuzz" "$fuzz_count" "$fuzz_seed"
cc -std=c11 -Wall -Wextra -Werror -O2 -o "$out/fuzz-runner" hardware/wifi/fuzz-runner.c
find "$out/fuzz" -name '*.bin' | sort | xargs "$out/fuzz-runner" >"$out/fuzz/c.txt"
if ! cmp -s "$out/fuzz/expected.txt" "$out/fuzz/c.txt"; then
  diff "$out/fuzz/expected.txt" "$out/fuzz/c.txt" | head -20 >&2
  echo "error: simulator and C executor disagree on fuzzed programs (seed $fuzz_seed)" >&2
  exit 1
fi
echo "device programs: $fuzz_count fuzzed programs agree (seed $fuzz_seed)"

# Generated executor vs handwritten executor vs Sim on the same corpus.
LEANOS_DEVICE_PROGRAM_CORPUS="$out/fuzz" ./scripts/check-generated-executor-host.sh

# Mutation self-test: each seeded executor bug (first occurrence of the
# pattern) must change some summary line or crash the runner.
mkdir -p "$out/mutant"
cp hardware/wifi/fuzz-runner.c hardware/wifi/fuzz-model.h "$out/mutant/"
killed=0
total=0
while IFS='@' read -r original mutated; do
  [[ "$original" == '//'* ]] && continue
  total=$((total + 1))
  python3 - "$original" "$mutated" "$out/mutant/wifi-exec.h" <<'PY'
import sys
source = open('hardware/wifi/wifi-exec.h').read()
original, mutated, target = sys.argv[1:4]
if original not in source:
    sys.exit(f'error: mutant pattern no longer occurs in wifi-exec.h: {original}')
open(target, 'w').write(source.replace(original, mutated, 1))  # first occurrence
PY
  cc -std=c11 -O2 -w -o "$out/mutant/fuzz-runner" "$out/mutant/fuzz-runner.c"
  if find "$out/fuzz" -name '*.bin' | sort | xargs "$out/mutant/fuzz-runner" >"$out/mutant/c.txt" 2>/dev/null &&
      cmp -s "$out/fuzz/expected.txt" "$out/mutant/c.txt"; then
    echo "error: fuzzing missed executor mutant $total: $original -> $mutated" >&2
    exit 1
  fi
  killed=$((killed + 1))
done < tests/fixtures/wifi-exec-mutants.txt
echo "device programs: fuzzing caught $killed/$total executor mutants"

# Hook mutation self-test (issue #494): each seeded bug in a C hook of the
# generated executor (tests/fixtures/wifi-gen-exec-mutants.txt) must change
# some summary line, so the differential still covers the trusted hooks.
prefix="$(lake env lean --print-prefix)"
gmut="$out/gen-mutant"
mkdir -p "$gmut/hardware/wifi" "$gmut/tests"
cp hardware/wifi/wifi-exec.h hardware/wifi/fuzz-model.h "$gmut/hardware/wifi/"
cp tests/device-program-exec-host.c "$gmut/tests/"
printf 'void leanos_register_boundary_target(const char *n, void *a);\n%s\n' \
  'void leanos_register_boundary_target(const char *n, void *a) { (void)n; (void)a; }' \
  >"$gmut/register.c"
cc -std=c11 -O2 -w -ffunction-sections -fdata-sections -I"$prefix/include" \
  -c .lake/build/ir/LeanOS/Wifi/Exec.c -o "$gmut/exec.o"
cc -std=c11 -O2 -w -c "$gmut/register.c" -o "$gmut/register.o"
gkilled=0
gtotal=0
while IFS='@' read -r original mutated; do
  [[ "$original" == '//'* ]] && continue
  gtotal=$((gtotal + 1))
  python3 - "$original" "$mutated" "$gmut/hardware/wifi/wifi-gen-exec.h" <<'PY'
import sys
source = open('hardware/wifi/wifi-gen-exec.h').read()
original, mutated, target = sys.argv[1:4]
if original not in source:
    sys.exit(f'error: mutant pattern no longer occurs in wifi-gen-exec.h: {original}')
open(target, 'w').write(source.replace(original, mutated, 1))  # first occurrence
PY
  cc -std=c11 -O2 -w -ffunction-sections -fdata-sections -Ibuild/boundary-abi \
    -c "$gmut/tests/device-program-exec-host.c" -o "$gmut/host.o"
  cc -Wl,--gc-sections "$gmut/host.o" "$gmut/register.o" "$gmut/exec.o" -o "$gmut/host"
  if LEANOS_DEVICE_PROGRAM_CORPUS="$out/fuzz" timeout 120 "$gmut/host" >/dev/null 2>&1; then
    echo "error: the generated-executor differential missed hook mutant $gtotal: $original -> $mutated" >&2
    exit 1
  fi
  gkilled=$((gkilled + 1))
done < tests/fixtures/wifi-gen-exec-mutants.txt
echo "device programs: the generated-executor differential caught $gkilled/$gtotal hook mutants"
