#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

check_timing_file="${LEANOS_CHECK_TIMING_FILE:-build/ci/check-phases.tsv}"
check_failure_timing_file="${LEANOS_CHECK_FAILURE_TIMING_FILE:-build/ci/check-failure.tsv}"
mkdir -p "$(dirname "$check_timing_file")"
mkdir -p "$(dirname "$check_failure_timing_file")"
rm -f "$check_failure_timing_file"
printf 'phase\tphase_seconds\ttotal_seconds\n' >"$check_timing_file"
check_started_at=$SECONDS
check_phase_started_at=$SECONDS
check_phase="lean-and-generated-contracts"
negative_log=""

record_check_failure() {
  local status=$?
  if [[ -n "$negative_log" ]]; then
    rm -f "$negative_log"
  fi
  if ((status != 0)); then
    local now=$SECONDS
    printf 'phase\tphase_seconds\ttotal_seconds\texit_code\n%s\t%s\t%s\t%s\n' \
      "$check_phase" "$((now - check_phase_started_at))" \
      "$((now - check_started_at))" "$status" >"$check_failure_timing_file"
  fi
  exit "$status"
}

trap record_check_failure EXIT

record_check_phase() {
  local phase="$1"
  local now=$SECONDS
  printf '%s\t%s\t%s\n' \
    "$phase" "$((now - check_phase_started_at))" "$((now - check_started_at))" \
    >>"$check_timing_file"
  check_phase_started_at=$now
}

./scripts/test-generate-oracle-adapter-map.sh

./scripts/test-native-decide-policy.sh
./scripts/check-native-decide-policy.py

lake build
negative_fixture_aggregator="LeanOS/NegativeFixtures.lean"
while IFS= read -r fixture; do
  fixture_module="${fixture%.lean}"
  fixture_module="${fixture_module//\//.}"
  if ! grep -Fxq "import ${fixture_module}" "$negative_fixture_aggregator"; then
    echo "error: ${fixture} is missing from ${negative_fixture_aggregator}" >&2
    exit 1
  fi
done < <(find LeanOS/NegativeFixtures -type f -name '*.lean' | sort)
lake build LeanOS.NegativeFixtures
lake build leanos-boot-plan
lake build leanos-vtd-plan
./scripts/test-generate-boundary-vocabulary.sh
./scripts/test-generate-serial-protocol.sh
python3 ./scripts/test-scenario-manifest.py

./scripts/check-security-claims.sh

./scripts/check-iotlb-authority-front-door.sh

./scripts/test-generate-invariants.sh

./scripts/check-invariants.sh

record_check_phase lean-and-generated-contracts
check_phase="security-and-platform-contracts"

./tests/test-q35-pci-construction.py
./scripts/test-q35-platform.sh
python3 ./scripts/test-kvm-preflight.py
./scripts/test-multivcpu-qmp.py
./scripts/test-run-multivcpu-rejection.sh
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

./scripts/check-firmware-corpus.sh

record_check_phase security-and-platform-contracts
check_phase="hosted-boundary-and-boot-contracts"

./scripts/check-boot-memory-full-projection.sh

./scripts/check-boot-handoff-stream.sh

./scripts/test-selected-compiler-propagation.sh

record_check_phase hosted-boundary-and-boot-contracts
check_phase="image-and-emulator-contracts"

# Run the compiler-failure fixture once in the required proof lane, not in
# every image-consuming QEMU shard. Keep it sequential with other build users.
./scripts/test-build-image.sh

./scripts/test-run-malformed-handoff.sh

./scripts/test-run-image.sh
./scripts/check-expectation-templates.sh

./scripts/test-browser-boot.sh

./scripts/test-run-extended-state-image.sh
./scripts/test-run-extended-state-peer-pke.sh

./scripts/test-run-fast-entry-image.sh

./scripts/test-run-preemption-image.sh
./scripts/test-run-frame-budget.sh
./scripts/test-run-capability-transfer.sh
./scripts/test-run-inflight-revocation.sh

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
python3 scripts/test-workflow-yaml.py
python3 scripts/test-setup-lean-cache.py

./scripts/test-main-ruleset-policy.py

./scripts/test-toolchain-profile.py
./scripts/render-toolchain-consumers.py --check
./scripts/test-render-toolchain-consumers.py

python3 scripts/check-adr-links.py
python3 scripts/test-adr-links.py

./scripts/test-build-timing.py

python3 scripts/test-check-timing.py

./scripts/test-image-bundle.sh

./scripts/run-emulator-evidence.py check

record_check_phase image-and-emulator-contracts
check_phase="proof-integrity-and-negative-fixtures"

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

rm -f "$negative_log"
negative_log=""
record_check_phase proof-integrity-and-negative-fixtures
python3 scripts/check-check-timing.py "$check_timing_file"
trap - EXIT

echo "Lean build, proof-integrity, and negative regression checks passed"
