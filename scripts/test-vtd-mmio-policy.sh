#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
elf="${1:-build/boot/leanos.elf}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

./scripts/check-vtd-mmio-policy.sh "$elf" >/dev/null

expect_rejected() {
  local name="$1" diagnostic="$2"
  if LEANOS_KERNEL_SOURCE="$tmp/kernel.c" \
      ./scripts/check-vtd-mmio-policy.sh "$elf" >"$tmp/$name.out" 2>&1; then
    echo "error: VT-d MMIO policy accepted mutated source: $name" >&2
    exit 1
  fi
  grep -Fq "$diagnostic" "$tmp/$name.out" || {
    echo "error: VT-d MMIO policy diagnostic drifted for: $name" >&2
    cat "$tmp/$name.out" >&2
    exit 1
  }
}

cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    vtd_mmio_write64\(iotlb, VTD_IOTLB_INVALIDATE \| VTD_IOTLB_GLOBAL\);/__SWAP__/;
   s/    vtd_mmio_write32\(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_TRANSLATION_ENABLE\);/    vtd_mmio_write64(iotlb, VTD_IOTLB_INVALIDATE | VTD_IOTLB_GLOBAL);/;
   s/__SWAP__/    vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_TRANSLATION_ENABLE);/' \
  "$tmp/kernel.c"
expect_rejected reordered-enable "source activation order drifted"

cp boot/kernel.c "$tmp/kernel.c"
sed -i 's|    verify_vtd_state();||' "$tmp/kernel.c"
expect_rejected omitted-gate "outbound re-verification is not exactly one gate call"

cp boot/kernel.c "$tmp/kernel.c"
sed -i 's|static __attribute__((noinline)) void vtd_boot_remap(void) {|static __attribute__((noinline)) void vtd_boot_remap(void) {\n    *(volatile uint32_t *)(__vtd_mmio_window_start + 0x18) = 0;|' \
  "$tmp/kernel.c"
expect_rejected rogue-derivation "MMIO window derivation is not confined"

cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    vtd_mmio_write64\(VTD_REG_CONTEXT_COMMAND,\n        VTD_CCMD_INVALIDATE \| VTD_CCMD_GLOBAL\);\n    vtd_wait_invalidation\(VTD_REG_CONTEXT_COMMAND, VTD_CCMD_INVALIDATE\);\n//' \
  "$tmp/kernel.c"
expect_rejected omitted-invalidation "drifted"

echo "VT-d MMIO policy positive and controlled-negative checks passed"
