#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
python3 scripts/qotom-ecam-fixture.py "$build/qotom-ecam-allocation.h"
python3 scripts/generate-qotom-ecam-firmware.py "$build/qotom-ecam-firmware-inputs.h"
flags=(-std=c11 -Wall -Wextra -Werror -Iboot -Ihardware/lab -I"$build")
case "$mode" in
  ordinary) cc="${CC:-cc}"; flags+=(-O2) ;;
  sanitizers)
    source scripts/hosted-sanitizer-config.sh
    leanos_assert_pinned_toolchain
    cc="$leanos_host_cc"
    flags+=("${leanos_host_sanitizer_flags[@]}")
    ;;
  *) echo 'error: expected ordinary or sanitizers' >&2; exit 1 ;;
esac
"$cc" "${flags[@]}" tests/qotom-ecam-read.c -o "$build/check"
if [[ "$mode" == sanitizers ]]; then
  leanos_run_sanitized "$build/check"
else
  "$build/check"
fi
"$cc" "${flags[@]}" tests/qotom-ecam-firmware.c -o "$build/firmware-check"
if [[ "$mode" == sanitizers ]]; then
  leanos_run_sanitized "$build/firmware-check"
else
  "$build/firmware-check"
fi
cat > "$build/freestanding.c" <<'C'
#include "qotom-ecam-read.h"
#include "qotom-ecam-firmware.h"
int firmware_matches(const struct lab_ecam_firmware_table *tables, uint32_t count) {
    return lab_ecam_firmware_matches(tables, count);
}
int read_config(void *context, uint8_t bus, uint8_t device, uint8_t function,
                uint8_t offset, uint32_t *value) {
    return qotom_ecam_read(context, bus, device, function, offset, value);
}
C
"$cc" -std=c11 -O2 -Wall -Wextra -Werror -ffreestanding -fno-builtin \
  -fno-stack-protector -Iboot -Ihardware/lab -I"$build" -c "$build/freestanding.c" -o "$build/freestanding.o"
[[ -z "$(nm -u "$build/freestanding.o")" ]] || {
  echo 'unexpected ECAM adapter runtime dependency' >&2; exit 1;
}
echo "Qotom ECAM $mode candidate checks PASS; access callback remains a caller obligation"
