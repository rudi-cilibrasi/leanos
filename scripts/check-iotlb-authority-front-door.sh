#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fail() {
  echo "error: IOTLB authority-front-door policy: $*" >&2
  exit 1
}

# IOMMU.lean defines the lower-level logical transitions and proves their
# properties. IOTLB.lean is the only implementation module allowed to invoke
# those transitions: it retains their successor behind an exact invalidation
# ticket and publishes it only after acknowledgement. SecurityClaims.lean may
# mention the lower-level gates in theorem statements, but no other production
# module may create a bypass around the cache-aware publication boundary.
mapfile -t bypasses < <(
  rg -l '\b(gatedByKernel|applyKernelOperation)\b' LeanOS \
    --glob '*.lean' \
    --glob '!IOMMU.lean' \
    --glob '!IOTLB.lean' \
    --glob '!SecurityClaims.lean' || true
)

if ((${#bypasses[@]} != 0)); then
  printf '%s\n' "${bypasses[@]}" >&2
  fail "lower-level authority publication escaped the reviewed modules"
fi

rg -Fq 'prepareControlPublication' LeanOS/IOTLB.lean ||
  fail "missing cache-aware IOMMU control preparation"
rg -Fq 'prepareAuthorityCleanupPublication' LeanOS/IOTLB.lean ||
  fail "missing cache-aware kernel cleanup preparation"
rg -Fq 'acknowledgeControlPublication' LeanOS/IOTLB.lean ||
  fail "missing exact control acknowledgement"
rg -Fq 'acknowledgeAuthorityCleanupPublication' LeanOS/IOTLB.lean ||
  fail "missing exact cleanup acknowledgement"
rg -Fq 'prepareAuthoritativePublication' LeanOS/IOTLB.lean ||
  fail "missing single authoritative preparation front door"
rg -Fq 'acknowledgeAuthoritativePublication' LeanOS/IOTLB.lean ||
  fail "missing single authoritative acknowledgement front door"

echo "IOTLB authority-front-door policy passed"
