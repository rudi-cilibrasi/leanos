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

# Fail fast on a missing host tool before any expensive work runs (issue #255).
require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: missing required tool '$1'; $2" >&2
    exit 1
  fi
}

require_tool node "install Node.js (CI uses actions/setup-node with node-version 22)"
require_tool python3 "install Ubuntu package python3"
require_tool sha256sum "install Ubuntu package coreutils"
require_tool git "install Ubuntu package git"

scenario="${LEANOS_BOOT_SCENARIO:-blocking-ipc}"
runtime_dir="${LEANOS_BROWSER_RUNTIME:-build/browser/runtime}"
source_manifest="$repo_root/browser-runtime/manifest-v1.json"
source_evidence="$repo_root/browser-runtime/provisional-source-build-evidence-v1.json"
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

image="${LEANOS_IMAGE:-build/boot/leanos-${LEANOS_VERSION:-0.1.0}-x86_64.iso}"
[[ -f "$image" ]] || { echo "error: missing canonical ISO: $image; run ./scripts/build-image.sh" >&2; exit 1; }
iso_sha="$(sha256sum "$image" | cut -d' ' -f1)"
wasm_sha="$(sha256sum "$runtime_dir/qemu-system-x86_64.wasm" | cut -d' ' -f1)"
browser_version="$("$browser" --version 2>/dev/null | head -n 1 || echo unknown)"
source_revision="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
runtime_provenance="$runtime_dir/.leanos-runtime-provenance.json"
if [[ -f "$runtime_provenance" ]]; then
  runtime_kind="$(python3 - "$runtime_provenance" "$runtime_dir" \
    "$source_manifest" "$source_evidence" <<'PY'
import hashlib, json, pathlib, sys
data = json.load(open(sys.argv[1]))
runtime = pathlib.Path(sys.argv[2])
manifest_path = pathlib.Path(sys.argv[3])
evidence_path = pathlib.Path(sys.argv[4])
if data.get("schema") != "leanos-browser-runtime-provenance/v1":
    raise SystemExit("error: invalid browser runtime provenance schema")
if data.get("kind") != "source-built":
    raise SystemExit("error: invalid browser runtime provenance kind")
manifest_digest = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
evidence_digest = hashlib.sha256(evidence_path.read_bytes()).hexdigest()
if data.get("manifest_sha256") != manifest_digest:
    raise SystemExit("error: source-built runtime provenance manifest digest mismatch")
if data.get("evidence_sha256") != evidence_digest:
    raise SystemExit("error: source-built runtime provenance evidence digest mismatch")
evidence = json.loads(evidence_path.read_text())
evidence_outputs = {item["path"]: item for item in evidence.get("outputs", [])}
name_map = {
    "out.js": "qemu-system-x86_64.js",
    "qemu-system-x86_64.wasm": "qemu-system-x86_64.wasm",
    "qemu-system-x86_64.worker.js": "qemu-system-x86_64.worker.js",
}
expected_names = {
    "out.js", "qemu-system-x86_64.wasm", "qemu-system-x86_64.worker.js"
}
if set(data.get("outputs", {})) != expected_names:
    raise SystemExit("error: incomplete source-built runtime provenance")
for name, expected in data["outputs"].items():
    path = runtime / name
    if not path.is_file():
        raise SystemExit(f"error: missing source-built runtime output: {name}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != expected.get("sha256") or path.stat().st_size != expected.get("size"):
        raise SystemExit(f"error: source-built runtime differs from provenance: {name}")
    retained = evidence_outputs.get(name_map[name])
    if retained is None or digest != retained.get("sha256") or path.stat().st_size != retained.get("size"):
        raise SystemExit(f"error: source-built runtime differs from retained evidence: {name}")
print(data["kind"])
PY
)"
  runtime_provenance_sha="$(sha256sum "$runtime_provenance" | cut -d' ' -f1)"
else
  runtime_kind="trusted-prebuilt"
  runtime_provenance_sha=""
fi

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
  "$browser_version" "$source_revision" "$scenario" "$runtime_kind" \
  "$runtime_provenance_sha" <<'PY'
import json, sys
path, status, elapsed, iso_sha, wasm_sha, browser, revision, scenario, runtime_kind, provenance_sha = sys.argv[1:11]
json.dump({
    "scenario": scenario,
    "result": "pass" if status == "0" else "fail",
    "runner_exit_status": int(status),
    "elapsed_seconds": int(elapsed),
    "iso_sha256": iso_sha,
    "qemu_wasm_wasm_sha256": wasm_sha,
    "browser_version": browser,
    "source_revision": revision,
    "runtime": runtime_kind,
    "runtime_provenance_sha256": provenance_sha or None,
    "acceptance": "scripts/run-image.sh canonical protocol + debug-exit 33",
}, open(path, "w"), indent=2)
open(path, "a").write("\n")
PY

if [[ $status -ne 0 ]]; then
  echo "browser boot FAILED (runner exit ${status}); evidence: ${evidence}" >&2
  exit 1
fi
echo "browser boot PASSED in ${elapsed}s; evidence: ${evidence}"
