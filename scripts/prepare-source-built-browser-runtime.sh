#!/usr/bin/env bash
# Replace only the emulator outputs in the pinned browser harness with an
# issue #194 source build whose complete prototype inventory and retained
# two-build evidence have already been verified.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source_dir="${1:-}"
runtime_dir="$repo_root/build/browser/runtime"
manifest="$repo_root/browser-runtime/manifest-v1.json"
evidence="$repo_root/browser-runtime/provisional-source-build-evidence-v1.json"

[[ -n "$source_dir" ]] || {
  echo "usage: $0 SOURCE_BUILD_OUTPUT_DIRECTORY" >&2
  exit 64
}
[[ "$source_dir" = /* ]] || source_dir="$PWD/$source_dir"
[[ -d "$source_dir" ]] || {
  echo "error: missing source-build output directory: $source_dir" >&2
  exit 1
}

"$repo_root/scripts/verify-qemu-wasm-manifest.py" \
  --prototype --staging "$source_dir"
"$repo_root/scripts/verify-qemu-wasm-manifest.py" \
  --evidence --staging "$source_dir"

# Reuse only the separately pinned support assets from the accepted #193
# harness. The support-only path never fetches or checks out its prebuilt
# emulator; the three emulator outputs come exclusively from source_dir.
"$repo_root/scripts/prepare-browser-runtime.sh" --support-only
install -m 0644 "$source_dir/qemu-system-x86_64.js" "$runtime_dir/out.js"
install -m 0644 "$source_dir/qemu-system-x86_64.wasm" \
  "$runtime_dir/qemu-system-x86_64.wasm"
install -m 0644 "$source_dir/qemu-system-x86_64.worker.js" \
  "$runtime_dir/qemu-system-x86_64.worker.js"

python3 - "$manifest" "$evidence" "$runtime_dir" <<'PY'
import hashlib
import json
import pathlib
import sys

manifest_path = pathlib.Path(sys.argv[1])
evidence_path = pathlib.Path(sys.argv[2])
runtime = pathlib.Path(sys.argv[3])
evidence = json.loads(evidence_path.read_text())

name_map = {
    "qemu-system-x86_64.js": "out.js",
    "qemu-system-x86_64.wasm": "qemu-system-x86_64.wasm",
    "qemu-system-x86_64.worker.js": "qemu-system-x86_64.worker.js",
}
expected = {item["path"]: item for item in evidence["outputs"]}
observed = {}
for source_name, staged_name in name_map.items():
    item = expected[source_name]
    path = runtime / staged_name
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != item["sha256"] or path.stat().st_size != item["size"]:
        raise SystemExit(f"error: staged source output differs: {staged_name}")
    observed[staged_name] = {"sha256": digest, "size": path.stat().st_size}

marker = {
    "schema": "leanos-browser-runtime-provenance/v1",
    "kind": "source-built",
    "manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
    "evidence_sha256": hashlib.sha256(evidence_path.read_bytes()).hexdigest(),
    "outputs": observed,
}
(runtime / ".leanos-runtime-provenance.json").write_text(
    json.dumps(marker, indent=2, sort_keys=True) + "\n"
)
PY

echo "Staged verified source-built qemu-wasm outputs in build/browser/runtime"
