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
"$cc" "${flags[@]}" tests/qotom-ecam-memory.c -o "$build/memory-check"
if [[ "$mode" == sanitizers ]]; then
  leanos_run_sanitized "$build/memory-check"
else
  "$build/memory-check"
fi
"$cc" "${flags[@]}" tests/qotom-ecam-window.c -o "$build/window-check"
if [[ "$mode" == sanitizers ]]; then
  leanos_run_sanitized "$build/window-check"
else
  "$build/window-check"
fi
"$cc" "${flags[@]}" tests/qotom-ecam-root.c -o "$build/root-check"
if [[ "$mode" == sanitizers ]]; then
  leanos_run_sanitized "$build/root-check"
else
  "$build/root-check"
fi
"$cc" "${flags[@]}" tests/qotom-ecam-arm.c -o "$build/arm-check"
if [[ "$mode" == sanitizers ]]; then
  leanos_run_sanitized "$build/arm-check"
else
  "$build/arm-check"
fi
cat > "$build/freestanding.c" <<'C'
#include "qotom-ecam-arm.h"
int arm(struct lab_ecam_window *window, const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables, uint32_t count, uint64_t address) {
    return lab_ecam_arm(window, view, tables, count, address);
}
#include "qotom-ecam-root.h"
int root_matches(const struct lab_ecam_root_view *view, uint64_t root, uint64_t window) {
    return lab_ecam_root_matches(view, root, window);
}
#include "qotom-ecam-read.h"
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-memory.h"
#include "qotom-ecam-window.h"
int window_read(void *context, uint64_t address, uint32_t *value) {
    return lab_ecam_window_read(context, address, value);
}
int controls_match(const struct lab_ecam_controls *controls, uint64_t root) {
    return lab_ecam_controls_match(controls, root);
}
int make_read_leaf(uint64_t address, uint64_t *leaf) {
    return lab_ecam_read_leaf(address, leaf);
}
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
