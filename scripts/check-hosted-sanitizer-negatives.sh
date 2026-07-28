#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
source scripts/hosted-sanitizer-config.sh
leanos_assert_pinned_toolchain
build=build/hosted-sanitizer-negatives
rm -rf "$build"
mkdir -p "$build"

common_negative_flags=(
  -O1
  -g3
  -fno-omit-frame-pointer
  -fno-optimize-sibling-calls
  -fno-sanitize-recover=all
)
"$leanos_host_cc" -std=c11 -Wall -Wextra -Werror \
  "${common_negative_flags[@]}" -fsanitize=address \
  tests/hosted-sanitizer-negative.c -o "$build/negative-address"
"$leanos_host_cc" -std=c11 -Wall -Wextra -Werror \
  "${common_negative_flags[@]}" -fsanitize=undefined \
  tests/hosted-sanitizer-negative.c -o "$build/negative-undefined"

run_negative() {
  local fixture="$1"
  local diagnostic="$2"
  local log="$build/$fixture.log"
  set +e
  leanos_run_sanitized "$build/negative-$fixture" "$fixture" >"$log" 2>&1
  local status=$?
  set -e
  [[ "$status" -ne 0 ]] || {
    echo "error: controlled sanitizer fixture '$fixture' unexpectedly passed" >&2
    exit 1
  }
  grep -Fq "$diagnostic" "$log" || {
    echo "error: controlled sanitizer fixture '$fixture' lacked '$diagnostic'" >&2
    cat "$log" >&2
    exit 1
  }
}
run_negative address "AddressSanitizer: heap-buffer-overflow"
run_negative undefined "runtime error: shift exponent"

"$leanos_host_cc" -std=c11 -O1 -frecord-gcc-switches \
  -c tests/hosted-sanitizer-negative.c -o "$build/unsanitized.o"
instrumentation_log="$build/unsanitized-object.log"
if leanos_require_sanitized_object "$build/unsanitized.o" \
    >"$instrumentation_log" 2>&1; then
  echo "error: unsanitized generated-object surrogate was accepted" >&2
  exit 1
fi
grep -Fq "compiled without pinned sanitizers" "$instrumentation_log" || {
  echo "error: unsanitized-object fixture lacked its expected diagnostic" >&2
  cat "$instrumentation_log" >&2
  exit 1
}

"$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" \
  -c tests/hosted-sanitizer-negative.c -o "$build/instrumented.o"
runtime_log="$build/omitted-runtime.log"
if "$leanos_host_cc" -fno-sanitize=all "$build/instrumented.o" \
    -o "$build/omitted-runtime" >"$runtime_log" 2>&1; then
  echo "error: instrumented fixture linked without the sanitizer runtime" >&2
  exit 1
fi
grep -Eq '__asan_|__ubsan_' "$runtime_log" || {
  echo "error: omitted-runtime fixture lacked sanitizer-symbol diagnostics" >&2
  cat "$runtime_log" >&2
  exit 1
}

{
  printf 'source-revision: '
  git rev-parse HEAD
  "$leanos_host_cc" --version | head -n 1
  printf 'compiler-package: gcc-13=%s\n' \
    "$(dpkg-query -W -f='${Version}' gcc-13)"
  printf 'asan-package: libasan8=%s\n' \
    "$(dpkg-query -W -f='${Version}' libasan8)"
  printf 'ubsan-package: libubsan1=%s\n' \
    "$(dpkg-query -W -f='${Version}' libubsan1)"
  printf 'compile-flags:'
  printf ' %q' "${leanos_host_sanitizer_flags[@]}"
  printf '\nASAN_OPTIONS=%s\nUBSAN_OPTIONS=%s\n' \
    "$leanos_host_asan_options" "$leanos_host_ubsan_options"
} > "$build/configuration.txt"

echo "Hosted sanitizer controlled-negative evidence passed"
