#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
build=build/pci-capabilities
mkdir -p "$build"
"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror tests/pci-capabilities.c -o "$build/ordinary"
"$build/ordinary"
source scripts/hosted-sanitizer-config.sh
leanos_assert_pinned_toolchain
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  tests/pci-capabilities.c -o "$build/sanitized"
leanos_run_sanitized "$build/sanitized"
printf '%s\n' 'PASS bounded capability lists: maximum size, cycles, read failures, pointer bounds, drift and backward links'

"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror -Iboot tests/qotom-pci-capabilities-lab.c -o "$build/lab-ordinary"
"$build/lab-ordinary"
"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  -Iboot tests/qotom-pci-capabilities-lab.c -o "$build/lab-sanitized"
leanos_run_sanitized "$build/lab-sanitized"
