#!/usr/bin/env bash
# Device-program gate (LeanOS/Wifi, LeanOS/Usb, hardware/wifi): the generator
# admits every firmware-free program under its target's confinement policy
# (LeanOS/DeviceProgramConfinement.lean), and the executor every LeanOS
# kernel boots agrees with LeanOS/Wifi/Sim.lean on the computation-only
# cross-check program and on random programs. That executor's step is
# generated (issue #494: the compiled LeanOS.Wifi.Exec.step, proved equal to
# Sim.step); the handwritten C around it is the image parser of
# hardware/wifi/wifi-exec.h and the hooks and step loop of
# hardware/wifi/wifi-gen-exec.h. The fuzz corpus (issue #451) is a regression
# test of the compiler path and that C, and its power over the handwritten C
# is checked: every mutant in tests/fixtures/wifi-exec-mutants.txt (parser)
# and tests/fixtures/wifi-gen-exec-mutants.txt (hooks, step loop) must be
# caught. scripts/check-generated-executor-host.sh also checks the generated
# step's freestanding boot shape and runs the hosted boundary row.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
out=build/ci/device-programs
rm -rf "$out"
mkdir -p "$out"

lake build leanos-wifi-gen leanos-wifi-xcheck leanos-wifi-fuzz LeanOS.Wifi.Exec
prefix="$(lake env lean --print-prefix)"
for program in probe sprom tables kbd ahci-identify rtl8168-arp; do
  .lake/build/bin/leanos-wifi-gen "$program" "$out/$program.bin" >/dev/null
  # Version-3 header: the image carries its checked policy.
  version="$(od -An -tu4 -j4 -N4 "$out/$program.bin" | tr -d ' ')"
  if [[ "$version" != 3 ]]; then
    echo "error: $program image is version $version, expected 3 (policy header)" >&2
    exit 1
  fi
done

# The generated step, linked into every hosted runner. Section GC drops the
# module initializer, its only reference to the Lean runtime.
cc -std=c11 -O2 -w -ffunction-sections -fdata-sections -I"$prefix/include" \
  -c .lake/build/ir/LeanOS/Wifi/Exec.c -o "$out/exec.o"
# build_runner source output [cflags...]
build_runner() {
  local source="$1" output="$2"
  shift 2
  cc -std=c11 -O2 -ffunction-sections -fdata-sections "$@" -c "$source" -o "$output.o"
  cc -Wl,--gc-sections "$output.o" "$out/exec.o" -o "$output"
}

build_runner hardware/wifi/host-runner.c "$out/host-runner" -Wall -Wextra -Werror
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

# Fuzz regression: simulator vs the generated executor on random images.
fuzz_count="${LEANOS_WIFI_FUZZ_COUNT:-3000}"
fuzz_seed="${LEANOS_WIFI_FUZZ_SEED:-451}"
.lake/build/bin/leanos-wifi-fuzz "$out/fuzz" "$fuzz_count" "$fuzz_seed"
find "$out/fuzz" -name '*.bin' | sort >"$out/fuzz-images.txt"
build_runner hardware/wifi/fuzz-runner.c "$out/fuzz-runner" -Wall -Wextra -Werror
xargs -a "$out/fuzz-images.txt" "$out/fuzz-runner" >"$out/fuzz/c.txt"
if ! cmp -s "$out/fuzz/expected.txt" "$out/fuzz/c.txt"; then
  diff "$out/fuzz/expected.txt" "$out/fuzz/c.txt" | head -20 >&2
  echo "error: simulator and generated executor disagree on fuzzed programs (seed $fuzz_seed)" >&2
  exit 1
fi
echo "device programs: $fuzz_count fuzzed programs agree (seed $fuzz_seed)"

# Freestanding boot shape, and the hosted boundary row on the same corpus.
LEANOS_DEVICE_PROGRAM_CORPUS="$out/fuzz" ./scripts/check-generated-executor-host.sh

# Mutation self-test of the handwritten C: each seeded bug (the first
# occurrence of the pattern in the named header is replaced) must change some
# summary line, crash the runner or make it time out.
# run_mutants fixture header
run_mutants() {
  local fixture="$1" header="$2" mdir="$out/mutant" killed=0 total=0
  local original mutated
  while IFS='@' read -r original mutated; do
    [[ "$original" == '//'* ]] && continue
    total=$((total + 1))
    rm -rf "$mdir"
    mkdir -p "$mdir"
    cp hardware/wifi/fuzz-runner.c hardware/wifi/fuzz-model.h hardware/wifi/wifi-exec.h \
      hardware/wifi/wifi-gen-exec.h "$mdir/"
    python3 - "$original" "$mutated" "hardware/wifi/$header" "$mdir/$header" <<'PY'
import sys
original, mutated, source_path, target = sys.argv[1:5]
source = open(source_path).read()
if original not in source:
    sys.exit(f'error: mutant pattern no longer occurs in {source_path}: {original}')
open(target, 'w').write(source.replace(original, mutated, 1))  # first occurrence
PY
    build_runner "$mdir/fuzz-runner.c" "$mdir/fuzz-runner" -w
    if timeout 120 xargs -a "$out/fuzz-images.txt" "$mdir/fuzz-runner" >"$mdir/c.txt" 2>/dev/null &&
        cmp -s "$out/fuzz/expected.txt" "$mdir/c.txt"; then
      echo "error: fuzzing missed $header mutant $total: $original -> $mutated" >&2
      exit 1
    fi
    killed=$((killed + 1))
  done <"$fixture"
  echo "device programs: fuzzing caught $killed/$total $header mutants"
}
# The image parser and wifi_start (hardware/wifi/wifi-exec.h).
run_mutants tests/fixtures/wifi-exec-mutants.txt wifi-exec.h
# The hook primitives and the step loop (hardware/wifi/wifi-gen-exec.h).
run_mutants tests/fixtures/wifi-gen-exec-mutants.txt wifi-gen-exec.h
