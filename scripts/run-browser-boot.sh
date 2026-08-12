#!/usr/bin/env bash
# Boot the unchanged canonical LeanOS ISO in the pinned qemu-wasm browser
# runtime and require the same complete versioned serial protocol plus
# debug-exit status 33 as the native reference (ADR 0011 media gate 1,
# issue #193).
#
# Acceptance is delegated to the unchanged scripts/run-image.sh by pointing its
# emulator at the QEMU-shaped browser shim through LEANOS_QEMU.  The browser run
# therefore inherits the canonical expected-protocol comparison, the DMA
# quarantine snapshot, and the VT-d activation snapshot without any
# browser-only acceptance string.  A firmware banner, timeout, or partial
# transcript cannot pass, exactly as for a native run.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

scenario="${LEANOS_BOOT_SCENARIO:-blocking-ipc}"
runtime_dir="build/browser/runtime"
shim="$repo_root/scripts/browser-boot/qemu-wasm-shim.mjs"
evidence="${LEANOS_BROWSER_EVIDENCE:-build/browser/browser-boot-${scenario}.json}"

[[ -d "$runtime_dir" ]] || { echo "error: run ./scripts/prepare-browser-runtime.sh first" >&2; exit 1; }
[[ -x "$shim" ]] || chmod +x "$shim"

browser="${LEANOS_BROWSER:-}"
if [[ -z "$browser" ]]; then
  browser="$(find "${LEANOS_BROWSER_ROOT:-build/browser/chrome}" -type f -name chrome 2>/dev/null | head -n 1 || true)"
fi
[[ -n "$browser" && -x "$browser" ]] || {
  echo "error: set LEANOS_BROWSER to the pinned Chrome-for-Testing binary" >&2
  echo "  npx --yes @puppeteer/browsers install chrome@stable --path build/browser/chrome" >&2
  exit 1
}
export LEANOS_BROWSER="$browser"

image="${LEANOS_IMAGE:-build/boot/leanos-$(cat VERSION 2>/dev/null || echo 0.1.0)-x86_64.iso}"
[[ -f "$image" ]] || { echo "error: missing canonical ISO: $image; run ./scripts/build-image.sh" >&2; exit 1; }
iso_sha="$(sha256sum "$image" | cut -d' ' -f1)"
wasm_sha="$(sha256sum "$runtime_dir/qemu-system-x86_64.wasm" | cut -d' ' -f1)"
browser_version="$("$browser" --version 2>/dev/null | head -n 1 || echo unknown)"
source_revision="$(git rev-parse HEAD 2>/dev/null || echo unknown)"

echo "Booting ${image} (sha ${iso_sha:0:16}...) in ${browser_version}"
start="$(date +%s)"
set +e
LEANOS_QEMU="$shim" \
LEANOS_QEMU_TIMEOUT_SECONDS="${LEANOS_QEMU_TIMEOUT_SECONDS:-240}" \
LEANOS_BOOT_SCENARIO="$scenario" \
LEANOS_IMAGE="$image" \
  ./scripts/run-image.sh "$image"
status=$?
set -e
elapsed=$(( "$(date +%s)" - start ))

mkdir -p "$(dirname "$evidence")"
python3 - "$evidence" "$status" "$elapsed" "$iso_sha" "$wasm_sha" \
  "$browser_version" "$source_revision" "$scenario" <<'PY'
import json, sys
path, status, elapsed, iso_sha, wasm_sha, browser, revision, scenario = sys.argv[1:9]
json.dump({
    "scenario": scenario,
    "result": "pass" if status == "0" else "fail",
    "runner_exit_status": int(status),
    "elapsed_seconds": int(elapsed),
    "iso_sha256": iso_sha,
    "qemu_wasm_wasm_sha256": wasm_sha,
    "browser_version": browser,
    "source_revision": revision,
    "runtime": "qemu-wasm 8.2.0 prebuilt (ktock/qemu-wasm-demo 0208c86, images b7c549b)",
    "acceptance": "scripts/run-image.sh canonical protocol + debug-exit 33",
}, open(path, "w"), indent=2)
open(path, "a").write("\n")
PY

if [[ $status -ne 0 ]]; then
  echo "browser boot FAILED (runner exit ${status}); evidence: ${evidence}" >&2
  exit 1
fi
echo "browser boot PASSED in ${elapsed}s; evidence: ${evidence}"
