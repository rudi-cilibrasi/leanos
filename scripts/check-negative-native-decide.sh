#!/usr/bin/env bash
set -euo pipefail

log_dir="$1"
category="$2"
fixture="$3"
fixture_path="tests/negative/${fixture}.lean"
fixture_log="${log_dir}/${fixture}.log"

if lake env lean "$fixture_path" >"$fixture_log" 2>&1; then
  echo "error: ${category} fixture ${fixture} unexpectedly type-checked" >&2
  exit 1
fi

requires_false_proposition=true
case "$fixture" in
  # This fixture is rejected while elaborating the proposition, before the
  # native_decide tactic can run.  Preserve its exact type-mismatch assertion
  # below instead of requiring a second, unreachable tactic diagnostic.
  IOMMUDetachedAuthoritativeProjection) requires_false_proposition=false ;;
esac

if ! grep -Fq "$fixture_path" "$fixture_log" ||
    { [[ "$requires_false_proposition" == true ]] &&
      { ! grep -Fq 'error: Tactic `native_decide` evaluated that the proposition' \
          "$fixture_log" || ! grep -Fq 'is false' "$fixture_log"; }; }; then
  echo "error: ${category} fixture ${fixture} lacked its expected semantic diagnostic" >&2
  cat "$fixture_log" >&2
  exit 1
fi

case "$fixture" in
  DMAEmptyInventory) expected='(validate emptySnapshot).isAccepted = true' ;;
  DMAInvalidControlContinuation) expected='q35BusMasterBitFlipSnapshot)).result = RuntimeResult.continued' ;;
  DMAEncodingImpliesValidation) expected='(validate staleSnapshot).isAccepted = true' ;;
  IOMMUDetachedAuthoritativeProjection) expected='state.iommu.Invariant ∧ state.Coherent' ;;
  IOMMUDeviceReadOutsideRule) expected='iova := 16' ;;
  IOMMUPermissionAmplification) expected='permission := readWrite' ;;
  IOMMUReleaseReachableFrame) expected='gate readOnlyState (Operation.releaseFrame' ;;
  IOMMURepeatRelease) expected='gate releasedFrameState (Operation.releaseFrame' ;;
  IOMMUSameOwnerWrongFrame) expected='validateCore sameOwnerWrongFrameCore = true' ;;
  IOMMUStaleBDFReuse) expected='(deviceRead reassignedState readRequest).isObserved = true' ;;
  IOMMUTwoLiveFrameGenerations) expected='validateCore twoLiveGenerationsCore = true' ;;
  DirectPortExposedBitmap) expected='executeUser state exposed request' ;;
  DirectPortWrongPurpose) expected='wrongPurpose).result = Result.kernelAccepted' ;;
  DirectPortWrongWidth) expected='wrongWidth).result = Result.kernelAccepted' ;;
  DirectPortContainmentExposedControls) expected='.port.result =' ;;
  *) expected='' ;;
esac

if [[ -n "$expected" ]] && ! grep -Fq "$expected" "$fixture_log"; then
  echo "error: ${category} fixture ${fixture} lacked its specialized diagnostic" >&2
  cat "$fixture_log" >&2
  exit 1
fi
