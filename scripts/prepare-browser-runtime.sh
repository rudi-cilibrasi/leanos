#!/usr/bin/env bash
# Stage the pinned, unforked qemu-wasm browser runtime for the LeanOS
# compatibility harness (issue #193).  Every redistributed asset is fetched at
# an immutable revision and verified against scripts/browser-boot/manifest.json;
# a single hash mismatch aborts.  The prebuilt WebAssembly artifact is trusted,
# not reproduced (issue #194 covers a reproducible source build).
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

support_only=false
case "${1:-}" in
  "") ;;
  --support-only) support_only=true ;;
  *) echo "usage: $0 [--support-only]" >&2; exit 64 ;;
esac

manifest="scripts/browser-boot/manifest.json"
runtime_dir="build/browser/runtime"
work_dir="build/browser/checkout"

json() { python3 - "$manifest" "$@" <<'PY'
import json, sys
data = json.load(open(sys.argv[1]))
node = data
for key in sys.argv[2:]:
    node = node[key]
print(node)
PY
}

demo_repo="$(json qemu_wasm_demo repository)"
demo_rev="$(json qemu_wasm_demo revision)"
images_rev="$(json qemu_wasm_demo images_submodule)"

echo "Preparing pinned qemu-wasm runtime (demo ${demo_rev}, images ${images_rev})"
rm -rf "$runtime_dir" "$work_dir"
mkdir -p "$runtime_dir" "$(dirname "$work_dir")"

git clone --quiet --filter=blob:none "$demo_repo" "$work_dir"
git -C "$work_dir" switch --quiet --detach "$demo_rev"
if $support_only; then
  # Keep the issue #194 source-build path from fetching or checking out the
  # prebuilt emulator. A blob-filtered sparse checkout materializes only the
  # separately pinned firmware-loader support files that path still needs.
  images_repo="$(git -C "$work_dir" config -f .gitmodules \
    --get submodule.docs/images.url)"
  rm -rf "$work_dir/docs/images"
  git clone --quiet --filter=blob:none --no-checkout \
    "$images_repo" "$work_dir/docs/images"
  git -C "$work_dir/docs/images" sparse-checkout init --no-cone
  git -C "$work_dir/docs/images" sparse-checkout set --no-cone \
    alpine-x86_64/load-rom.js alpine-x86_64/load-rom.data
  git -C "$work_dir/docs/images" switch --quiet --detach "$images_rev"
else
  git -C "$work_dir" submodule update --quiet --init --filter=blob:none docs/images
fi
observed_images="$(git -C "$work_dir/docs/images" rev-parse HEAD)"
[[ "$observed_images" == "$images_rev" ]] || {
  echo "error: images submodule ${observed_images} != pinned ${images_rev}" >&2
  exit 1
}

verify() {
  local name="$1" src="$2" expected="$3"
  [[ -f "$src" ]] || { echo "error: missing runtime input: $src" >&2; exit 1; }
  local observed
  observed="$(sha256sum "$src" | cut -d' ' -f1)"
  [[ "$observed" == "$expected" ]] || {
    echo "error: ${name} sha256 ${observed} != pinned ${expected}" >&2
    exit 1
  }
  cp "$src" "$runtime_dir/$name"
}

runtime_names=(coi-serviceworker.js load-rom.js load-rom.data)
if ! $support_only; then
  runtime_names+=(out.js qemu-system-x86_64.wasm qemu-system-x86_64.worker.js)
fi
for name in "${runtime_names[@]}"; do
  rel="$(json runtime_files "$name" path)"
  hash="$(json runtime_files "$name" sha256)"
  verify "$name" "$work_dir/$rel" "$hash"
done

# The terminal assets are fetched from their pinned unpkg releases and verified.
mapfile -t terminal_names < <(python3 - "$manifest" <<'PY'
import json, sys
data = json.load(open(sys.argv[1]))
print("\n".join(data["terminal_files"].keys()))
PY
)
for name in "${terminal_names[@]}"; do
  url="$(json terminal_files "$name" url)"
  hash="$(json terminal_files "$name" sha256)"
  curl --fail --silent --location --proto '=https' "$url" --output "$runtime_dir/$name"
  observed="$(sha256sum "$runtime_dir/$name" | cut -d' ' -f1)"
  [[ "$observed" == "$hash" ]] || {
    echo "error: ${name} sha256 ${observed} != pinned ${hash}" >&2
    exit 1
  }
done

( cd scripts/browser-boot && npm ci --ignore-scripts >/dev/null )

rm -rf "$work_dir"
echo "Staged verified $($support_only && echo support || echo runtime) assets in ${runtime_dir}:"
( cd "$runtime_dir" && sha256sum ./* )
