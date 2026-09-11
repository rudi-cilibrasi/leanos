#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:-ordinary}"
case "$mode" in ordinary|sanitized) ;; *) echo 'usage: build-qotom-bsp-replay.sh [ordinary|sanitized]' >&2; exit 2;; esac
build=build/qotom-bsp-replay
if [[ "$mode" == sanitized ]]; then build+=-sanitized; fi
bash scripts/build-qotom-bsp-object.sh "$build"
if [[ "$mode" == sanitized ]]; then
  source scripts/hosted-sanitizer-config.sh
  leanos_assert_pinned_toolchain
  "$leanos_host_cc" "${leanos_host_sanitizer_flags[@]}" -fno-pie \
    -I"$(lean --print-prefix)/include" -c "$build/QotomMadtStream.c" -o "$build/generated-sanitized.o"
  leanos_require_sanitized_object "$build/generated-sanitized.o"
  "$leanos_host_cc" "${leanos_host_sanitizer_flags[@]}" -fno-pie -no-pie \
    -Wall -Wextra -Werror -Ibuild/boundary-abi -Wl,--gc-sections \
    tests/qotom-bsp-replay.c "$build/generated-sanitized.o" -o "$build/host"
  leanos_run_sanitized "$build/host" --identity
  exit 0
fi
"${CC:-gcc}" -O2 -Wall -Wextra -Werror -no-pie -Ibuild/boundary-abi \
  tests/qotom-bsp-replay.c "$build/bsp.o" -o "$build/host"
"$build/host" --identity
