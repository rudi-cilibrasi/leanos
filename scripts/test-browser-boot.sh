#!/usr/bin/env bash
# Offline controlled fixtures for the qemu-wasm browser harness (issue #193).
# No browser or network is used: the browser driver's decision logic and
# argument translation are unit-tested directly, and the runtime-outcome exit
# codes are fed through the unchanged scripts/run-image.sh with a mock emulator
# to prove that a firmware-only transcript, a truncated protocol, a guest
# failure, a timeout, or a runtime abort cannot be accepted as a boot.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"

node scripts/browser-boot/test-evaluate.mjs

tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
printf '%040d\n' 0 > "$tmp/SOURCE_REVISION"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null

# A mock emulator honouring the shim's contract: answer --version, write the
# fixture serial to the -serial file: target, and exit with the fixture status.
mock="$tmp/mock-qemu.sh"
cat > "$mock" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${1:-}" == --version ]]; then echo "mock browser shim 1"; exit 0; fi
serial=""
prev=""
for arg in "$@"; do
  if [[ "$prev" == -serial && "$arg" == file:* ]]; then serial="${arg#file:}"; fi
  prev="$arg"
done
[[ -n "$serial" ]] || { echo "mock: no -serial file:" >&2; exit 64; }
mkdir -p "$(dirname "$serial")"
printf '%s' "${LEANOS_MOCK_SERIAL:-}" > "$serial"
exit "${LEANOS_MOCK_EXIT:-0}"
EOF
chmod +x "$mock"

firmware_only=$'SeaBIOS (version rel-1.16.3)\nBooting from DVD/CD...\n'
truncated=$'LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap\nLEANOS/15 DMA snapshot=1 topology=0001000800020002 bus=0\n'
guest_fail=$'LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap\nLEANOS/3 FINAL status=FAIL reason=vtd-live-status\n'

run_mock() {  # mode serial exitcode ; echoes run-image failure_class line
  local serial="$1" exit="$2"
  LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
  LEANOS_QEMU="$mock" \
  LEANOS_MOCK_SERIAL="$serial" \
  LEANOS_MOCK_EXIT="$exit" \
  LEANOS_QEMU_TIMEOUT_SECONDS=5 \
  LEANOS_SERIAL_LOG="$tmp/out.serial" \
  LEANOS_DMA_SNAPSHOT="$tmp/out.dma.tsv" \
  LEANOS_VTD_SNAPSHOT="$tmp/out.vtd.tsv" \
  LEANOS_SOURCE_REVISION_FILE="$tmp/SOURCE_REVISION" \
    ./scripts/run-image.sh "$tmp/image.iso" 2>&1 || true
}

expect_reject() {  # name serial exitcode
  local name="$1" serial="$2" exit="$3" output
  output="$(run_mock "$serial" "$exit")"
  if ! grep -q 'failure_class=' <<<"$output"; then
    echo "error: browser fixture '$name' was not rejected" >&2
    echo "$output" >&2
    exit 1
  fi
  echo "ok - rejects ${name}: $(grep -o 'failure_class=[a-z-]*' <<<"$output" | head -1)"
}

touch "$tmp/image.iso"
# Runtime-level failures the shim maps to distinct exit codes (guest debug-exit
# 33 with no/partial serial, guest fail 35, timeout 124, runtime abort 70).
expect_reject firmware-only-transcript "$firmware_only" 33
expect_reject truncated-protocol "$truncated" 33
expect_reject empty-serial-media-failure "" 33
expect_reject guest-failure-status "$guest_fail" 35
expect_reject boot-timeout "" 124
expect_reject runtime-abort "" 70

echo "Browser boot harness offline fixtures passed"
