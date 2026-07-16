#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build

./scripts/check-security-claims.sh

./scripts/check-oracle-host.sh

./scripts/test-run-image.sh

./scripts/test-run-double-fault.sh

lake env lean -DwarningAsError=true -R experiments/freestanding-boundary \
  experiments/freestanding-boundary/Boundary.lean
lake env lean -DwarningAsError=true -R experiments/hosted-boundary \
  experiments/hosted-boundary/Hosted.lean

declaration_escape_pattern='^[[:space:]]*((private|protected|local|noncomputable)[[:space:]]+)*(axiom|constant|unsafe|extern)[[:space:]]'
ffi_attribute_pattern='^[[:space:]]*@\[[^]]*(extern|implemented_by)([[:space:],(]|\])'

mapfile -d '' lean_sources < <(
  find LeanOS experiments -type f -name '*.lean' -print0
  printf '%s\0' LeanOS.lean
)

trusted_scan_log="$(mktemp)"
set +e
grep -En \
  -e "$declaration_escape_pattern" \
  -e "$ffi_attribute_pattern" \
  "${lean_sources[@]}" >"$trusted_scan_log"
trusted_scan_status=$?
set -e

if [[ "$trusted_scan_status" == 0 ]]; then
  cat "$trusted_scan_log"
  rm -f "$trusted_scan_log"
  echo "error: unapproved axiom or trusted-code declaration in Lean sources" >&2
  echo "document and explicitly allowlist required TCB declarations" >&2
  exit 1
elif [[ "$trusted_scan_status" != 1 ]]; then
  cat "$trusted_scan_log" >&2
  rm -f "$trusted_scan_log"
  echo "error: trusted-declaration scan could not inspect Lean sources" >&2
  exit 1
fi
rm -f "$trusted_scan_log"

negative_log="$(mktemp)"
trap 'rm -f "$negative_log"' EXIT

if lake env lean tests/negative/InvalidBound.lean >"$negative_log" 2>&1; then
  echo "error: negative proof fixture unexpectedly type-checked" >&2
  exit 1
fi

if ! grep -q 'tests/negative/InvalidBound.lean.*error:' "$negative_log"; then
  echo "error: negative proof fixture failed without the expected Lean diagnostic" >&2
  cat "$negative_log" >&2
  exit 1
fi

if lake env lean -DwarningAsError=true tests/negative/Sorry.lean \
    >"$negative_log" 2>&1; then
  echo "error: a declaration using sorry unexpectedly type-checked" >&2
  exit 1
fi

if ! grep -q 'declaration uses `sorry`' "$negative_log"; then
  echo "error: sorry fixture failed without the expected Lean diagnostic" >&2
  cat "$negative_log" >&2
  exit 1
fi

for fixture in WeakenedAuthorityClaim DroppedSeparationClaim; do
  if lake env lean "tests/negative/${fixture}.lean" >"$negative_log" 2>&1; then
    echo "error: security-claim fixture ${fixture} unexpectedly type-checked" >&2
    exit 1
  fi
  if ! grep -q "tests/negative/${fixture}.lean.*error: Type mismatch" "$negative_log"; then
    echo "error: security-claim fixture ${fixture} lacked the expected Lean diagnostic" >&2
    cat "$negative_log" >&2
    exit 1
  fi
done

if lake env lean tests/negative/VacuousClaimSetup.lean >"$negative_log" 2>&1; then
  echo "error: vacuous security-claim fixture unexpectedly type-checked" >&2
  exit 1
fi
if ! grep -q 'error: Type mismatch' "$negative_log" ||
    ! grep -q 'KernelTransition.Command.unsupported' "$negative_log"; then
  echo "error: vacuous security-claim fixture lacked its expected contradiction" >&2
  cat "$negative_log" >&2
  exit 1
fi

echo "Lean build, proof-integrity, and negative regression checks passed"
