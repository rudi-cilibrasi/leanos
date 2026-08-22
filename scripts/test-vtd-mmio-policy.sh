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
  's/    vtd_journal_record\(5\);\n\n    vtd_invalidate_global_iotlb\(\);/    vtd_journal_record(5);\n\nSWAP_MARKER/;
   s/    vtd_mmio_write32\(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_TRANSLATION_ENABLE\);/    vtd_invalidate_global_iotlb();/;
   s/SWAP_MARKER/    vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_TRANSLATION_ENABLE);/' \
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

# The assigned-EDU completion must not become authoritative before the old
# second-level entry is unpublished.  Move only that table clear after the
# completion result and prove the source-order gate rejects the mutation.
cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    \(\(volatile uint64_t \*\)vtd_second_level_table\)\[0\] = 0;\n/UNPUBLISH_MARKER\n/;
   s/(        fail\("vtd-reuse-model-completion"\);\n)/$1    ((volatile uint64_t *)vtd_second_level_table)[0] = 0;\n/;
   s/UNPUBLISH_MARKER\n//' \
  "$tmp/kernel.c"
expect_rejected reuse-completion-before-unpublish \
  "assigned-EDU frame-reuse source order drifted"

# Scrubbing is publication of a new lifetime, so it must remain gated by the
# exact invalidation completion.  Move the real scrub loop before the generated
# completion acknowledgement and require the same source-order policy to fail.
cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    for \(uint64_t word = 0; word < PAGE_BYTES \/ sizeof\(uint64_t\); \+\+word\)\n        read_buffer\[word\] = 0;\n/SCRUB_MARKER\n/;
   s/(    if \(leanos_assigned_edu_reuse_publication\(\n            2, 1, LEANOS_VTD_ASSIGNED_REQUESTER,)/    for (uint64_t word = 0; word < PAGE_BYTES \/ sizeof(uint64_t); ++word)\n        read_buffer[word] = 0;\n$1/;
   s/SCRUB_MARKER\n//' \
  "$tmp/kernel.c"
expect_rejected reuse-scrub-before-completion \
  "assigned-EDU frame-reuse source order drifted"

# Installing the fresh-owner leaf is the authoritative publication boundary.
# Move that real second-level-table write ahead of exact completion and prove
# the policy rejects reuse even when the later invalidation remains present.
cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    \(\(volatile uint64_t \*\)vtd_second_level_table\)\[2\] =\n        LEANOS_VTD_ASSIGNED_READ_BUFFER_FRAME \* PAGE_BYTES \+ 1;\n/REPUBLISH_MARKER\n/;
   s/(    if \(leanos_assigned_edu_reuse_publication\(\n            2, 1, LEANOS_VTD_ASSIGNED_REQUESTER,)/    ((volatile uint64_t *)vtd_second_level_table)[2] =\n        LEANOS_VTD_ASSIGNED_READ_BUFFER_FRAME * PAGE_BYTES + 1;\n$1/;
   s/REPUBLISH_MARKER\n//' \
  "$tmp/kernel.c"
expect_rejected reuse-republish-before-completion \
  "assigned-EDU frame-reuse source order drifted"

# The stale requester must be denied before the fresh authorized transfer can
# count as evidence.  Defer only the real fault-status rejection until after
# the fresh-transfer check and require the source-order policy to reject it.
cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    if \(fault_status != 2\)\n        fail\("vtd-reuse-old-iova-access"\);\n/OLD_DENIAL_MARKER\n/;
   s/(    if \(write_buffer\[0\] != secret0 \|\| write_buffer\[1\] != secret1 \|\|\n        read_buffer\[0\] != secret0 \|\| read_buffer\[1\] != secret1 \|\|\n        vtd_mmio_read32\(0x34\) != 0\)\n        fail\("vtd-reuse-fresh-iova-transfer"\);\n)/$1    if (fault_status != 2)\n        fail("vtd-reuse-old-iova-access");\n/;
   s/OLD_DENIAL_MARKER\n//' \
  "$tmp/kernel.c"
expect_rejected reuse-fresh-transfer-before-old-denial \
  "assigned-EDU frame-reuse source order drifted"

# A permanently disabled device must not count as safe reuse. Remove the real
# fresh-owner transfer validation and require the policy to reject the missing
# positive half of the old-denied/fresh-authorized evidence pair.
cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    if \(write_buffer\[0\] != secret0 \|\| write_buffer\[1\] != secret1 \|\|\n        read_buffer\[0\] != secret0 \|\| read_buffer\[1\] != secret1 \|\|\n        vtd_mmio_read32\(0x34\) != 0\)\n        fail\("vtd-reuse-fresh-iova-transfer"\);\n//' \
  "$tmp/kernel.c"
expect_rejected reuse-fresh-transfer-omitted \
  "assigned-EDU frame-reuse source order drifted"

# Restoring the old boot mapping is teardown, not evidence for the fresh
# lifetime. Move that exact table publication ahead of the fresh-transfer
# validation and require the source-order policy to reject the shortcut.
cp boot/kernel.c "$tmp/kernel.c"
perl -0pi -e \
  's/    \(\(volatile uint64_t \*\)vtd_second_level_table\)\[0\] =\n        leanos_vtd_assigned_second_level_table\[0\];\n    \(\(volatile uint64_t \*\)vtd_second_level_table\)\[2\] = 0;\n    __asm__ volatile\("" ::: "memory"\);\n/RESTORE_MARKER\n/;
   s/(    if \(write_buffer\[0\] != secret0 \|\| write_buffer\[1\] != secret1 \|\|\n        read_buffer\[0\] != secret0 \|\| read_buffer\[1\] != secret1 \|\|\n        vtd_mmio_read32\(0x34\) != 0\)\n        fail\("vtd-reuse-fresh-iova-transfer"\);\n)/    ((volatile uint64_t *)vtd_second_level_table)[0] =\n        leanos_vtd_assigned_second_level_table[0];\n    ((volatile uint64_t *)vtd_second_level_table)[2] = 0;\n    __asm__ volatile("" ::: "memory");\n$1/;
   s/RESTORE_MARKER\n//' \
  "$tmp/kernel.c"
expect_rejected reuse-restore-before-fresh-transfer \
  "assigned-EDU frame-reuse source order drifted"

echo "VT-d MMIO policy positive and controlled-negative checks passed"
