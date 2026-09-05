#!/usr/bin/env bash
# Assemble the self-contained, deployable LeanOS browser demo (issue #192).
#
# The staged site under build/browser/site/ contains only the hash-verified
# pinned runtime, the pinned terminal assets, the reviewed demo page, and the
# unchanged canonical ISO.  Every asset is served from the same origin: there
# are no remote runtime dependencies, so the deployed page never fetches code
# or data at load time.  The GitHub Pages workflow uploads this directory
# unchanged after the offline harness fixtures pass.
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# Fail fast on a missing host tool before any expensive work runs (issue #255).
require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: missing required tool '$1'; $2" >&2
    exit 1
  fi
}

require_tool python3 "install Ubuntu package python3"
require_tool sha256sum "install Ubuntu package coreutils"

runtime_dir="build/browser/runtime"
demo_dir="scripts/browser-boot/demo"
site_dir="build/browser/site"
manifest="scripts/browser-boot/manifest.json"

[[ -d "$runtime_dir" ]] || { echo "error: run ./scripts/prepare-browser-runtime.sh first" >&2; exit 1; }

image="${LEANOS_IMAGE:-build/boot/leanos-${LEANOS_VERSION:-0.1.0}-x86_64.iso}"
[[ -f "$image" ]] || { echo "error: missing canonical ISO: $image; run ./scripts/build-image.sh" >&2; exit 1; }

# Re-verify every runtime input against the manifest so a stale or tampered
# staging directory cannot be deployed.
python3 - "$manifest" "$runtime_dir" <<'PY'
import hashlib, json, pathlib, sys
manifest = json.load(open(sys.argv[1]))
runtime = pathlib.Path(sys.argv[2])
groups = ["runtime_files", "terminal_files"]
failures = []
for group in groups:
    for name, meta in manifest[group].items():
        path = runtime / name
        if not path.exists():
            failures.append(f"missing {name}")
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != meta["sha256"]:
            failures.append(f"{name} sha256 {digest} != pinned {meta['sha256']}")
if failures:
    print("error: staged runtime failed manifest verification:", file=sys.stderr)
    for line in failures:
        print(f"  {line}", file=sys.stderr)
    raise SystemExit(1)
print("runtime manifest verification passed")
PY

rm -rf "$site_dir"
mkdir -p "$site_dir"

# Pinned runtime + terminal assets loaded by the demo page, same origin only.
for name in coi-serviceworker.js out.js qemu-system-x86_64.wasm \
    qemu-system-x86_64.worker.js load-rom.js load-rom.data \
    xterm-pty.js xterm.js xterm.css; do
  cp "$runtime_dir/$name" "$site_dir/$name"
done
cp "$demo_dir/index.html" "$site_dir/index.html"
cp "$demo_dir/leanos-module.js" "$site_dir/leanos-module.js"
cp docs/browser-demo-licenses.md "$site_dir/LICENSES.md"
cp "$image" "$site_dir/leanos.iso"

iso_sha="$(sha256sum "$image" | cut -d' ' -f1)"
wasm_sha="$(sha256sum "$runtime_dir/qemu-system-x86_64.wasm" | cut -d' ' -f1)"
site_bytes="$(du -sb "$site_dir" | cut -f1)"

# GitHub enforces a 100 MiB single-object limit; the Pages site and repository
# limits are far larger.  The wasm and ISO are the only large objects.
max_object=$((100 * 1024 * 1024))
while IFS= read -r -d '' file; do
  size="$(stat -c%s "$file")"
  if (( size > max_object )); then
    echo "error: $(basename "$file") is ${size} bytes, over the 100 MiB object limit" >&2
    exit 1
  fi
done < <(find "$site_dir" -type f -print0)

python3 - "$site_dir/manifest.json" "$iso_sha" "$wasm_sha" "$site_bytes" \
  "$(git rev-parse HEAD 2>/dev/null || echo unknown)" <<'PY'
import json, sys
path, iso_sha, wasm_sha, site_bytes, revision = sys.argv[1:6]
json.dump({
    "description": "Deployable LeanOS qemu-wasm demo site staged by scripts/stage-browser-demo.sh",
    "source_revision": revision,
    "iso_sha256": iso_sha,
    "qemu_wasm_wasm_sha256": wasm_sha,
    "site_bytes": int(site_bytes),
    "runtime": "qemu-wasm 8.2.0 prebuilt (ktock/qemu-wasm-demo 0208c86, images b7c549b)",
    "acceptance": "boots the unchanged ISO to ${LEANOS_SERIAL_10_FINAL} status=PASS and debug-exit 33 (validated natively by scripts/run-image.sh and in-browser by scripts/run-browser-boot.sh)",
}, open(path, "w"), indent=2)
open(path, "a").write("\n")
PY

echo "Staged self-contained demo site in ${site_dir} ($(( site_bytes / 1024 / 1024 )) MiB):"
( cd "$site_dir" && ls -1 )
