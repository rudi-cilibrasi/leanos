#!/usr/bin/env bash
# Controlled runner negatives for the dedicated real-CPL3 stale-translation
# protocol. Each forged or incomplete transcript must fail closed.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"
printf '%040d\n' 0 >"$tmp/SOURCE_REVISION"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
${CC:-gcc} -nostdlib -no-pie -Wl,-e,_start -x c \
  -o "$tmp/stale-symbols.elf" - <<'EOF'
char page_map_level_4_b[4096];
char user_b_stale_translation_fault_instruction[8];
char user_b_stack_top[1];
void _start(void) {}
EOF

invoke() {
  local mode="$1"
  LEANOS_BOOT_SCENARIO=stale-translation-denial \
  LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
  LEANOS_QEMU="$root/tests/qemu-stale-translation-fixture.sh" \
  LEANOS_QEMU_FIXTURE_MODE="$mode" \
  LEANOS_QEMU_TIMEOUT_SECONDS=5 \
  LEANOS_SERIAL_LOG="$tmp/$mode.serial" \
  LEANOS_DMA_SNAPSHOT="$tmp/$mode.dma.tsv" \
  LEANOS_FAULT_CONTAINMENT_ELF="$tmp/stale-symbols.elf" \
  LEANOS_SOURCE_REVISION_FILE="$tmp/SOURCE_REVISION" \
  ./scripts/run-image.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
for spec in \
  'omitted-invalidation serial-protocol' \
  'wrong-page serial-protocol' \
  'wrong-root serial-protocol' \
  'invalidation-before-store serial-protocol' \
  'publication-before-invalidation serial-protocol' \
  'omitted-reuse serial-protocol' \
  'reuse-before-unmap serial-protocol' \
  'reuse-publication-before-canary serial-protocol' \
  'replacement-canary-corrupt serial-protocol' \
  'omitted-new-owner-read serial-protocol' \
  'new-owner-wrong-address-space serial-protocol' \
  'skipped-prefill serial-protocol' \
  'incidental-cr3-reload serial-protocol' \
  'software-walker-only serial-protocol' \
  'direct-called-page-fault serial-protocol' \
  'stale-access-succeeded serial-protocol' \
  'partial serial-protocol' \
  'reordered serial-protocol' \
  'guest-error guest-error' \
  'reset qemu-error' \
  'triple-fault qemu-error' \
  'hang timeout'; do
  read -r mode class <<<"$spec"
  set +e
  invoke "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$mode.output" || {
    echo "error: stale-translation fixture '$mode' expected failure_class=$class" >&2
    cat "$tmp/$mode.output" >&2
    exit 1
  }
done
echo "Stale-translation QEMU runner success and negative fixture checks passed"
