#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build
lake build leanos-boot-plan

./scripts/check-security-claims.sh

./tests/test-q35-pci-construction.py

./scripts/check-dma-quarantine-corpus.sh

./scripts/test-capability-boundaries.sh

./scripts/check-oracle-host.sh

./scripts/test-run-image.sh

./scripts/test-run-extended-state-image.sh

./scripts/test-run-fast-entry-image.sh

./scripts/test-run-preemption-image.sh

./scripts/test-run-fault-containment.sh

./scripts/test-run-double-fault.sh

./scripts/test-run-entry-stack-overflow.sh

./scripts/test-entry-stack-budget.sh

./scripts/test-entry-stack-layout.sh

./scripts/test-emulator-evidence.py

./scripts/run-emulator-evidence.py check

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

if lake env lean tests/negative/BootPageTablePlanMutation.lean \
    >"$negative_log" 2>&1; then
  echo "error: boot page-table plan mutation unexpectedly type-checked" >&2
  exit 1
fi

if ! grep -q "invalid .* notation.*constructor.*private" "$negative_log"; then
  echo "error: boot page-table plan mutation lacked the private-constructor diagnostic" >&2
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

if lake env lean tests/negative/DMAEmptyInventory.lean >"$negative_log" 2>&1; then
  echo "error: empty DMA inventory unexpectedly validated" >&2
  exit 1
fi
if ! grep -Fq 'error: Tactic `native_decide` evaluated that the proposition' \
    "$negative_log" ||
    ! grep -Fq '(validate emptySnapshot).isAccepted = true' "$negative_log" ||
    ! grep -Fq 'is false' "$negative_log"; then
  echo "error: empty DMA inventory lacked the expected semantic rejection" >&2
  cat "$negative_log" >&2
  exit 1
fi

for fixture in DMAWeakenedBusMaster DMADroppedFunction DMARuntimeEnable; do
  if lake env lean "tests/negative/${fixture}.lean" >"$negative_log" 2>&1; then
    echo "error: DMA quarantine fixture ${fixture} unexpectedly type-checked" >&2
    exit 1
  fi
  if ! grep -q "tests/negative/${fixture}.lean.*error:" "$negative_log"; then
    echo "error: DMA quarantine fixture ${fixture} lacked a Lean diagnostic" >&2
    cat "$negative_log" >&2
    exit 1
  fi
done

for fixture in DirectPortUserMutation DirectPortExposedBitmap \
    DirectPortWrongPurpose DirectPortWrongWidth; do
  if lake env lean "tests/negative/${fixture}.lean" >"$negative_log" 2>&1; then
    echo "error: direct-port-I/O fixture ${fixture} unexpectedly type-checked" >&2
    exit 1
  fi
  case "$fixture" in
    DirectPortUserMutation)
      expected_diagnostic='error: Type mismatch'
      expected_proposition='user_request_preserves_device_state state live request'
      expected_result='(executeUser state live request).state.devices ≠ state.devices'
      ;;
    DirectPortExposedBitmap)
      expected_diagnostic='error: Tactic `native_decide` evaluated that the proposition'
      expected_proposition='executeUser state exposed request = { state := state, result := Result.userDeniedGP }'
      expected_result='is false'
      ;;
    DirectPortWrongPurpose)
      expected_diagnostic='error: Tactic `native_decide` evaluated that the proposition'
      expected_proposition='(executeKernel state selectedControls wrongPurpose).result = Result.kernelAccepted'
      expected_result='is false'
      ;;
    DirectPortWrongWidth)
      expected_diagnostic='error: Tactic `native_decide` evaluated that the proposition'
      expected_proposition='(executeKernel state selectedControls wrongWidth).result = Result.kernelAccepted'
      expected_result='is false'
      ;;
  esac
  if ! grep -Fq "tests/negative/${fixture}.lean" "$negative_log" ||
      ! grep -Fq "$expected_diagnostic" "$negative_log" ||
      ! grep -Fq "$expected_proposition" "$negative_log" ||
      ! grep -Fq "$expected_result" "$negative_log"; then
    echo "error: direct-port-I/O fixture ${fixture} lacked its expected semantic diagnostic" >&2
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
