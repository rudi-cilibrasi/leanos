#!/usr/bin/env bash
# Run hosted C tests under CompCert's reference interpreter (ADR 0030, #597).
#
# `ccomp -interp` executes the C semantics QuickProof's theorems are about. A
# "Stuck state" is undefined behaviour in that semantics even where native
# runs under ASan/UBSan are clean (pointer-to-integer arithmetic, comparisons
# across objects, uninitialised reads). Optional, like scripts/check-quickproof.sh:
# it uses the QuickProof Docker image, whose CompCert is under the INRIA
# Non-Commercial License. Each test is pasted into one translation unit with
# QuickProof's plain-C memcpy/memset/... and a puts, which the interpreter lacks.
#
# usage: scripts/check-compcert-interp.sh [TEST.c...]   (default: experiments/quickproof/interp-tests.txt)
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image="${LEANOS_QUICKPROOF_IMAGE:-ghcr.io/genproof/quickproof@sha256:8d420bf40775d63aecf9475135e37167e1c1f96183617b853d9eac806aa6961a}"
budget="${LEANOS_INTERP_TIMEOUT:-900}"
tests=("$@")
if [[ ${#tests[@]} -eq 0 ]]; then
  while read -r t || [[ -n "$t" ]]; do [[ -z "$t" || "$t" == \#* ]] || tests+=("$t"); done \
    <"$root/experiments/quickproof/interp-tests.txt"
fi
work="$(mktemp -d "${TMPDIR:-/tmp}/leanos-interp.XXXXXX")"
trap 'rm -rf "$work"' EXIT
status=0
[[ ${#tests[@]} -gt 0 ]] || { echo "error: no tests to run" >&2; exit 1; }
for t in "${tests[@]}"; do
  case "$t" in /*) src="$t" ;; *) src="$root/$t" ;; esac
  unit="$work/$(basename "$t" .c).unity.c"
  printf '#include <stdio.h>\nint puts(const char *s) { return printf("%%s\\n", s); }\n#include "/opt/quickproof/libc/libc.c"\n#include "%s"\n' \
    "$src" >"$unit"
  if docker run --rm --user "$(id -u):$(id -g)" -v "$work:$work" -v "$root:$root:ro" \
      -w "$root" --entrypoint /bin/bash "$image" -lc \
      "timeout $budget ccomp -interp -fstruct-passing -fbitfields -Iboot -Iinclude -Ibuild/boot $unit" \
      >"$work/log" 2>&1 && grep -q 'program terminated (exit code = 0)' "$work/log"; then
    echo "ok    $t"
  else
    echo "FAIL  $t: $(grep -v warning "$work/log" | grep -m1 -E 'Stuck|ERROR|error' || echo 'no clean termination')"
    status=1
  fi
done
exit "$status"
