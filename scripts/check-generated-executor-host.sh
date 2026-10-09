#!/usr/bin/env bash
# Generated device-program executor (issue #494, ADR 0020).
#
# `leanos_device_program_step` is the C the Lean compiler generates for
# LeanOS.Wifi.Exec.step, which LeanOS.Wifi.ExecRefinement.step_eq proves equal
# to Sim.step. This gate checks the two things the proof cannot:
#
# 1. Boot shape: compiled with the boot image's code-generation flags and
#    linked freestanding with -nostdlib --gc-sections (together with the C
#    hooks of hardware/wifi/wifi-gen-exec.h in the kernel's direct-hook
#    configuration), the generated step needs no Lean runtime or libc symbol
#    and contains no indirect branch (the entry-stack gate's ban; no jump
#    table).
# 2. Hosted differential (the hosted generated-boundary row
#    `device-program-step`): on the fuzz corpus of tests/WifiFuzz.lean the
#    generated executor, the handwritten wifi-exec.h and Sim print identical
#    summary lines. During the transition this diffs the generated executor
#    against the handwritten one; afterwards it is a regression test.
#
# usage: check-generated-executor-host.sh [ordinary|sanitized]
# LEANOS_DEVICE_PROGRAM_CORPUS names an existing corpus directory (as
# scripts/check-device-programs.sh passes); otherwise one is generated.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
case "$mode" in
  ordinary|sanitized) ;;
  *)
    echo "usage: $0 [ordinary|sanitized]" >&2
    exit 2
    ;;
esac

lake build LeanOS.Wifi.Exec leanos-wifi-fuzz >/dev/null
prefix="$(lake env lean --print-prefix)"
./scripts/generate-oracle.sh build/boundary-abi

if [[ "$mode" == ordinary ]]; then
  out=build/generated-executor-freestanding
  rm -rf "$out"
  mkdir -p "$out"
  cc="${LEANOS_CC:-cc}"
  flags=(-m64 -std=c11 -ffreestanding -fno-stack-protector -fno-pic -mno-red-zone
    -mgeneral-regs-only -ffunction-sections -fdata-sections -O2 -I"$prefix/include")
  if "$cc" --version | sed -n '1p' | grep -qi clang; then
    flags+=(-ffp-eval-method=source -Wno-error=pragmas -fno-jump-tables)
  fi
  "$cc" "${flags[@]}" -c .lake/build/ir/LeanOS/Wifi/Exec.c -o "$out/exec.o"
  "$cc" "${flags[@]}" -Wall -Wextra -Werror -Wno-unused-function -Ibuild/boundary-abi \
    -c tests/device-program-exec-freestanding.c -o "$out/harness.o"
  "$cc" -m64 -nostdlib -static -no-pie -Wl,--gc-sections -Wl,-e,_start \
    "$out/harness.o" "$out/exec.o" -o "$out/exec.elf"
  undefined="$(nm -u "$out/exec.elf")"
  if [[ -n "$undefined" ]]; then
    echo "error: the freestanding generated executor has undefined symbols:" >&2
    echo "$undefined" >&2
    exit 1
  fi
  # The generated step and its specialized loops: no indirect jump or call.
  objdump -d --no-show-raw-insn "$out/exec.elf" >"$out/exec.dis"
  python3 - "$out/exec.dis" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
functions = re.split(r'\n(?=[0-9a-f]+ <)', text)
generated = [f for f in functions
             if re.match(r'[0-9a-f]+ <(leanos_device_program_step|l[a-z]*_[A-Za-z_]*LeanOS_Wifi_Exec_[^>]*)>:', f)]
if not any(f.split('<', 1)[1].startswith('leanos_device_program_step>') for f in generated):
    sys.exit('error: leanos_device_program_step is missing from the freestanding link')
for f in generated:
    name = f.split('<', 1)[1].split('>', 1)[0]
    for line in f.splitlines():
        if re.search(r'\b(jmp|call)q?\s+\*', line):
            sys.exit(f'error: indirect branch in generated {name}: {line.strip()}')
print(f'generated executor: freestanding link has no undefined symbols; '
      f'{len(generated)} generated functions, no indirect branch')
PY
fi

corpus="${LEANOS_DEVICE_PROGRAM_CORPUS:-}"
if [[ -z "$corpus" ]]; then
  corpus="build/generated-executor-corpus"
  if [[ "$mode" == ordinary || ! -f "$corpus/expected.txt" ]]; then
    rm -rf "$corpus"
    .lake/build/bin/leanos-wifi-fuzz "$corpus" "${LEANOS_WIFI_FUZZ_COUNT:-600}" \
      "${LEANOS_WIFI_FUZZ_SEED:-451}" >/dev/null
  fi
fi
[[ -f "$corpus/expected.txt" ]] || {
  echo "error: device-program corpus $corpus lacks expected.txt" >&2
  exit 1
}
LEANOS_DEVICE_PROGRAM_CORPUS="$(cd "$corpus" && pwd)" \
  LEANOS_HOSTED_BOUNDARY_ID=device-program-step \
  ./scripts/check-boot-handoff-host.sh "$mode"
