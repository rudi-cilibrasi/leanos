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

# The source-built staging path must not route through the legacy mode that
# checks out the trusted prebuilt emulator before replacing it.
grep -Fq 'prepare-browser-runtime.sh" --support-only' \
  scripts/prepare-source-built-browser-runtime.sh
grep -Fq 'sparse-checkout set --no-cone' scripts/prepare-browser-runtime.sh
if sed -n '/if \$support_only;/,/^else$/p' scripts/prepare-browser-runtime.sh | \
    grep -Eq 'out\.js|qemu-system-x86_64\.(wasm|worker\.js)'; then
  echo "error: support-only staging references a prebuilt emulator output" >&2
  exit 1
fi
echo "ok - source-built staging excludes prebuilt emulator outputs"

tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
printf '%040d\n' 0 > "$tmp/SOURCE_REVISION"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null

# A marker that merely blesses substituted bytes must not authenticate itself.
for name in out.js qemu-system-x86_64.wasm qemu-system-x86_64.worker.js; do
  printf 'forged-%s\n' "$name" > "$tmp/$name"
done
python3 - "$tmp" <<'PY'
import hashlib, json, pathlib, sys
runtime = pathlib.Path(sys.argv[1])
outputs = {}
for name in ("out.js", "qemu-system-x86_64.wasm", "qemu-system-x86_64.worker.js"):
    path = runtime / name
    outputs[name] = {
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "size": path.stat().st_size,
    }
(runtime / ".leanos-runtime-provenance.json").write_text(json.dumps({
    "schema": "leanos-browser-runtime-provenance/v1",
    "kind": "source-built",
    "manifest_sha256": "0" * 64,
    "evidence_sha256": "0" * 64,
    "outputs": outputs,
}) + "\n")
PY
fake_browser="$tmp/fake-browser"
printf '#!/usr/bin/env bash\necho fake-browser\n' > "$fake_browser"
chmod +x "$fake_browser"
touch "$tmp/image.iso"
if LEANOS_BROWSER_RUNTIME="$tmp" LEANOS_BROWSER="$fake_browser" \
    LEANOS_IMAGE="$tmp/image.iso" ./scripts/run-browser-boot.sh \
    >"$tmp/forged.out" 2>&1; then
  echo "error: forged source-built provenance marker was accepted" >&2
  exit 1
fi
grep -Fq 'source-built runtime provenance manifest digest mismatch' \
  "$tmp/forged.out" || {
    echo "error: forged marker lacked the expected fail-closed diagnostic" >&2
    cat "$tmp/forged.out" >&2
    exit 1
  }
echo "ok - rejects self-authenticating source-built provenance marker"

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

# The public demo must run the same reviewed q35 machine as the native
# emulator: the pinned intel-iommu unit, one vCPU, no network, and the
# debug-exit device the acceptance gate reads. Guard against silent drift to a
# weaker browser-only machine.
demo_module="scripts/browser-boot/demo/leanos-module.js"
demo_pins=(
  "intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,dma-translation=on,snoop-control=off"
  "isa-debug-exit,iobase=0xf4,iosize=0x04"
  "'-smp', '1'"
  "'-nic', 'none'"
  "'-machine', 'q35,accel=tcg'"
)
for pin in "${demo_pins[@]}"; do
  grep -Fq "$pin" "$demo_module" || {
    echo "error: demo machine drifted from the reviewed q35 construction: missing '$pin'" >&2
    exit 1
  }
done
echo "ok - public demo pins the reviewed q35 + intel-iommu construction"

echo "Browser boot harness offline fixtures passed"
