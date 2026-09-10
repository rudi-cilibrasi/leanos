#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
python3 scripts/pci-enumeration-fixture.py "$build/pci-enumeration-capture.h"
flags=(-std=c11 -Wall -Wextra -Werror -Iboot -I"$build")
case "$mode" in
  ordinary)
    cc="${CC:-cc}"
    flags+=(-O2)
    ;;
  sanitizers)
    source scripts/hosted-sanitizer-config.sh
    leanos_assert_pinned_toolchain
    cc="$leanos_host_cc"
    flags+=("${leanos_host_sanitizer_flags[@]}")
    ;;
  *) echo "error: expected ordinary or sanitizers" >&2; exit 1 ;;
esac
"$cc" "${flags[@]}" tests/pci-enumeration.c -o "$build/check"
if [[ "$mode" == sanitizers ]]; then
  leanos_run_sanitized "$build/check"
else
  "$build/check"
fi
# Compile the actual collector independently of the hosted test runtime.
cat > "$build/freestanding.c" <<'C'
#include "pci-enumeration.h"
struct pci_enumeration_result collect(pci_enumeration_read read, void *context,
                                     struct pci_enumeration_snapshot *snapshot) {
    return pci_enumerate_segment(read, context, snapshot);
}
C
"$cc" -std=c11 -O2 -Wall -Wextra -Werror -ffreestanding -fno-builtin \
  -fno-stack-protector -Iboot -c "$build/freestanding.c" -o "$build/freestanding.o"
undefined="$(nm -u "$build/freestanding.o")"
[[ -z "$undefined" ]] || { echo "unexpected runtime dependency: $undefined" >&2; exit 1; }
echo "PCI enumeration $mode checks passed; freestanding object has no runtime dependencies"
