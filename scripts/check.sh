#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build
lake build leanos-boot-plan
lake build leanos-vtd-plan

./scripts/check-security-claims.sh

./scripts/check-iotlb-authority-front-door.sh

./scripts/test-generate-invariants.sh

./scripts/check-invariants.sh

./tests/test-q35-pci-construction.py
./scripts/test-q35-platform.sh
./scripts/test-run-dma-unknown-device.sh

./scripts/test-qemu-wasm-manifest.sh

./scripts/check-dma-quarantine-corpus.sh

./scripts/test-capability-boundaries.sh

./scripts/test-hosted-boundary-harness-scan.sh

if [[ "${LEANOS_SKIP_HOSTED_BOUNDARY_REPLAY:-0}" != 1 ]]; then
  ./scripts/check-hosted-generated-boundaries.sh ordinary

  ./scripts/check-hosted-generated-boundaries.sh sanitized

  ./scripts/check-hosted-sanitizer-negatives.sh
fi

./scripts/check-boot-memory-full-projection.sh

./scripts/check-boot-handoff-stream.sh

./scripts/test-selected-compiler-propagation.sh

./scripts/test-run-malformed-handoff.sh

./scripts/test-run-image.sh

./scripts/test-browser-boot.sh

./scripts/test-run-extended-state-image.sh

./scripts/test-run-fast-entry-image.sh

./scripts/test-run-preemption-image.sh
./scripts/test-run-frame-budget.sh

./scripts/test-run-fault-containment.sh
./scripts/test-run-fault-integrity.sh

./scripts/test-run-direct-port-pic.sh

./scripts/test-run-integer-fault.sh

./scripts/test-run-stale-translation.sh

./scripts/test-run-double-fault.sh

./scripts/test-run-entry-stack-overflow.sh

./scripts/test-run-nmi.sh

./scripts/test-run-bootstrap32-ud.sh

./scripts/test-run-bootstrap64-nmi.sh

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
negative_log_dir="$(mktemp -d)"
negative_jobs="${LEANOS_NEGATIVE_JOBS:-$(nproc)}"
if [[ ! "$negative_jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "error: LEANOS_NEGATIVE_JOBS must be a positive integer" >&2
  exit 1
fi
trap 'rm -f "$negative_log"; rm -rf "$negative_log_dir"' EXIT

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

if lake env lean tests/negative/VTdBootPlanForgedContext.lean \
    >"$negative_log" 2>&1; then
  echo "error: VT-d boot plan context forgery unexpectedly type-checked" >&2
  exit 1
fi
if ! grep -q "invalid .* notation.*constructor.*private" "$negative_log"; then
  echo "error: VT-d boot plan context forgery lacked the private-constructor diagnostic" >&2
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

for fixture in WeakenedAuthorityClaim DroppedSeparationClaim UnsynchronizedBlockingIPC \
    CallerSuppliedCompositeContext TautologicalAuthoritativeContract \
    UniversalAuthoritativePreservation GenericCompositeSuccess \
    DroppedFaultClassKernelOrigin AuthoritativeUnmapRejectedMutation; do
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

awk 'NF == 2 && $1 !~ /^#/ { print $1, $2 }' \
  tests/negative/native-decide-fixtures.tsv |
  xargs -r -n 2 -P "$negative_jobs" \
    ./scripts/check-negative-native-decide.sh "$negative_log_dir"

if lake env lean tests/negative/PageFaultAgreementWriteInstructionContainment.lean \
    >"$negative_log" 2>&1; then
  echo "error: impossible write/instruction page fault unexpectedly contained" >&2
  exit 1
fi
if ! grep -Fq 'tests/negative/PageFaultAgreementWriteInstructionContainment.lean' \
      "$negative_log" ||
    ! grep -Fq 'error: Type mismatch' "$negative_log" ||
    ! grep -Fq 'pageFaultImpossibleWriteInstructionContained = true' "$negative_log" ||
    ! grep -Fq 'pageFaultImpossibleWriteInstructionContained = false' "$negative_log"; then
  echo "error: impossible write/instruction fixture lacked its expected fatal diagnostic" >&2
  cat "$negative_log" >&2
  exit 1
fi

for fixture in DMAWeakenedBusMaster DMADroppedFunction DMARuntimeEnable DMATraceMutation \
    DMAGlobalControlMutation; do
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

if lake env lean tests/negative/DMADeviceReadConfidentiality.lean \
    >"$negative_log" 2>&1; then
  echo "error: DMA device-read confidentiality overclaim unexpectedly type-checked" >&2
  exit 1
fi
if ! grep -Fq 'has type' "$negative_log" ||
    ! grep -Fq 'observedByte := 0 } ≠ { observedByte := 1' "$negative_log" ||
    ! grep -Fq 'observedByte := 0 } = { observedByte := 1' "$negative_log"; then
  echo "error: DMA confidentiality fixture lacked the expected semantic mismatch" >&2
  cat "$negative_log" >&2
  exit 1
fi

for fixture in IOMMUOmittedSourceBinding IOMMUFabricatedReadView; do
  if lake env lean "tests/negative/${fixture}.lean" >"$negative_log" 2>&1; then
    echo "error: IOMMU confinement fixture ${fixture} unexpectedly type-checked" >&2
    exit 1
  fi
  case "$fixture" in
    IOMMUOmittedSourceBinding)
      expected_diagnostic='Fields missing: `assignmentFound`, `mappingFound`, `frameFound`, `sourceBound`'
      ;;
    IOMMUFabricatedReadView)
      expected_diagnostic='Fields missing: `bytes`, `observed`'
      ;;
  esac
  if ! grep -Fq "tests/negative/${fixture}.lean" "$negative_log" ||
      ! grep -Fq "$expected_diagnostic" "$negative_log"; then
    echo "error: IOMMU confinement fixture ${fixture} lacked its expected semantic diagnostic" >&2
    cat "$negative_log" >&2
    exit 1
  fi
done

for fixture in DirectPortUserMutation; do
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

for fixture in NMIFrameMissingRip NMIFrameMissingCs NMIFrameMissingFlags \
    NMIFrameMissingRsp NMIFrameMissingSs; do
  if lake env lean "tests/negative/${fixture}.lean" >"$negative_log" 2>&1; then
    echo "error: structural NMI fixture ${fixture} unexpectedly type-checked" >&2
    exit 1
  fi
  case "$fixture" in
    NMIFrameMissingRip) expected_field='`rip`' ;;
    NMIFrameMissingCs) expected_field='`cs`' ;;
    NMIFrameMissingFlags) expected_field='`flags`' ;;
    NMIFrameMissingRsp) expected_field='`rsp`' ;;
    NMIFrameMissingSs) expected_field='`ss`' ;;
  esac
  if ! grep -Fq "tests/negative/${fixture}.lean" "$negative_log" ||
      ! grep -Fq 'error: Fields missing' "$negative_log" ||
      ! grep -Fq "$expected_field" "$negative_log"; then
    echo "error: structural NMI fixture ${fixture} lacked its missing-frame-word diagnostic" >&2
    cat "$negative_log" >&2
    exit 1
  fi
done

for fixture in NMIHaltClearing NMIPostHaltRepair; do
  if lake env lean "tests/negative/${fixture}.lean" >"$negative_log" 2>&1; then
    echo "error: post-halt NMI fixture ${fixture} unexpectedly type-checked" >&2
    exit 1
  fi
  if ! grep -Fq "tests/negative/${fixture}.lean" "$negative_log" ||
      ! grep -Fq 'error: unsolved goals' "$negative_log"; then
    echo "error: post-halt NMI fixture ${fixture} lacked its absorption diagnostic" >&2
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
