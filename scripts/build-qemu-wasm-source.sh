#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
manifest="$repo_root/browser-runtime/manifest-v1.json"
output="${1:-$repo_root/build/qemu-wasm-source}"
runtime_dir="$repo_root/browser-runtime"

if [[ "$output" != /* ]]; then
  output="$repo_root/$output"
fi
mkdir -p "$(dirname "$output")"
output="$(cd "$(dirname "$output")" && pwd)/$(basename "$output")"

"$repo_root/scripts/verify-qemu-wasm-manifest.py" --inputs

command -v docker >/dev/null || {
  echo "error: docker is required" >&2
  exit 1
}
command -v git >/dev/null || {
  echo "error: git is required" >&2
  exit 1
}
command -v jq >/dev/null || {
  echo "error: jq is required" >&2
  exit 1
}

platform="$(jq -r '.toolchain.container.platform' "$manifest")"
repository="$(jq -r '.sources[] | select(.name == "qemu-wasm") | .repository' "$manifest")"
revision="$(jq -r '.sources[] | select(.name == "qemu-wasm") | .revision' "$manifest")"
tree="$(jq -r '.sources[] | select(.name == "qemu-wasm") | .tree' "$manifest")"
dtc_repository="$(jq -r '.sources[] | select(.name == "dtc") | .repository' "$manifest")"
dtc_revision="$(jq -r '.sources[] | select(.name == "dtc") | .revision' "$manifest")"
dtc_tree="$(jq -r '.sources[] | select(.name == "dtc") | .tree' "$manifest")"
keymap_repository="$(jq -r '.sources[] | select(.name == "keycodemapdb") | .repository' "$manifest")"
keymap_revision="$(jq -r '.sources[] | select(.name == "keycodemapdb") | .revision' "$manifest")"
keymap_tree="$(jq -r '.sources[] | select(.name == "keycodemapdb") | .tree' "$manifest")"
softfloat_repository="$(jq -r '.sources[] | select(.name == "berkeley-softfloat-3") | .repository' "$manifest")"
softfloat_revision="$(jq -r '.sources[] | select(.name == "berkeley-softfloat-3") | .revision' "$manifest")"
softfloat_tree="$(jq -r '.sources[] | select(.name == "berkeley-softfloat-3") | .tree' "$manifest")"
testfloat_repository="$(jq -r '.sources[] | select(.name == "berkeley-testfloat-3") | .repository' "$manifest")"
testfloat_revision="$(jq -r '.sources[] | select(.name == "berkeley-testfloat-3") | .revision' "$manifest")"
testfloat_tree="$(jq -r '.sources[] | select(.name == "berkeley-testfloat-3") | .tree' "$manifest")"
extra_cflags="$(jq -r '.configuration.extra_cflags' "$manifest")"
extra_ldflags="$(jq -r '.configuration.extra_ldflags' "$manifest")"
configure_command="$(jq -r '.configuration.configure_command' "$manifest")"
build_command="$(jq -r '.configuration.build_command' "$manifest")"
manifest_hash="$(sha256sum "$manifest" | cut -d ' ' -f 1)"
image="leanos-qemu-wasm-build:${manifest_hash}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
source_dir="$work/qemu-wasm"
mkdir "$source_dir"
git -C "$source_dir" init --quiet
git -C "$source_dir" remote add origin "$repository"
git -C "$source_dir" fetch --quiet --depth=1 origin "$revision"
git -C "$source_dir" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$source_dir" rev-parse HEAD)" = "$revision"
test "$(git -C "$source_dir" rev-parse HEAD^{tree})" = "$tree"
test ! -e "$source_dir/qemu-system-x86_64.wasm"
dtc_dir="$source_dir/subprojects/dtc"
mkdir "$dtc_dir"
git -C "$dtc_dir" init --quiet
git -C "$dtc_dir" remote add origin "$dtc_repository"
git -C "$dtc_dir" fetch --quiet --depth=1 origin "$dtc_revision"
git -C "$dtc_dir" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$dtc_dir" rev-parse HEAD)" = "$dtc_revision"
test "$(git -C "$dtc_dir" rev-parse HEAD^{tree})" = "$dtc_tree"
keymap_dir="$source_dir/subprojects/keycodemapdb"
mkdir "$keymap_dir"
git -C "$keymap_dir" init --quiet
git -C "$keymap_dir" remote add origin "$keymap_repository"
git -C "$keymap_dir" fetch --quiet --depth=1 origin "$keymap_revision"
git -C "$keymap_dir" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$keymap_dir" rev-parse HEAD)" = "$keymap_revision"
test "$(git -C "$keymap_dir" rev-parse HEAD^{tree})" = "$keymap_tree"
softfloat_dir="$source_dir/subprojects/berkeley-softfloat-3"
mkdir "$softfloat_dir"
git -C "$softfloat_dir" init --quiet
git -C "$softfloat_dir" remote add origin "$softfloat_repository"
git -C "$softfloat_dir" fetch --quiet --depth=1 origin "$softfloat_revision"
git -C "$softfloat_dir" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$softfloat_dir" rev-parse HEAD)" = "$softfloat_revision"
test "$(git -C "$softfloat_dir" rev-parse HEAD^{tree})" = "$softfloat_tree"
cp -a "$source_dir/subprojects/packagefiles/berkeley-softfloat-3/." "$softfloat_dir/"
testfloat_dir="$source_dir/subprojects/berkeley-testfloat-3"
mkdir "$testfloat_dir"
git -C "$testfloat_dir" init --quiet
git -C "$testfloat_dir" remote add origin "$testfloat_repository"
git -C "$testfloat_dir" fetch --quiet --depth=1 origin "$testfloat_revision"
git -C "$testfloat_dir" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$testfloat_dir" rev-parse HEAD)" = "$testfloat_revision"
test "$(git -C "$testfloat_dir" rev-parse HEAD^{tree})" = "$testfloat_tree"
cp -a "$source_dir/subprojects/packagefiles/berkeley-testfloat-3/." "$testfloat_dir/"

docker build \
  --platform "$platform" \
  --provenance=false \
  --file "$runtime_dir/Dockerfile" \
  --tag "$image" \
  "$runtime_dir"
image_id="$(docker image inspect --format '{{.Id}}' "$image")"

mkdir -p "$output"
test -z "$(find "$output" -mindepth 1 -maxdepth 1 -print -quit)"

docker run --rm \
  --platform "$platform" \
  --volume "$source_dir:/src:ro" \
  --volume "$output:/out" \
  --env EXTRA_CFLAGS="$extra_cflags" \
  --env EXTRA_LDFLAGS="$extra_ldflags" \
  --env CONFIGURE_COMMAND="$configure_command" \
  --env BUILD_COMMAND="$build_command" \
  --env BUILD_CONTAINER_IMAGE_ID="$image_id" \
  "$image" \
  bash -euo pipefail -c '
    eval "$CONFIGURE_COMMAND"
    eval "$BUILD_COMMAND"
    test -f qemu-system-x86_64
    test -f qemu-system-x86_64.wasm
    test -f qemu-system-x86_64.worker.js
    cp qemu-system-x86_64 /out/qemu-system-x86_64.js
    cp qemu-system-x86_64.wasm qemu-system-x86_64.worker.js /out/
    {
      printf "container-image-id: %s\n" "$BUILD_CONTAINER_IMAGE_ID"
      emcc --version | sed -n "1p"
      { emconfigure --version 2>&1 || true; } | sed -n "1p"
      { emmake --version 2>&1 || true; } | sed -n "1p"
      meson --version
      ninja --version
      python3 --version
      node --version
      npm --version
      dpkg-query -W
    } > /out/TOOLCHAIN.txt
  '

{
  printf 'manifest-sha256: %s\n' "$manifest_hash"
  printf 'container-tag: %s\n' "$image"
  printf 'container-image-id: %s\n' "$image_id"
  printf 'platform: %s\n' "$platform"
  printf 'source-repository: %s\n' "$repository"
  printf 'source-revision: %s\n' "$revision"
  printf 'source-tree: %s\n' "$tree"
  printf 'dtc-repository: %s\n' "$dtc_repository"
  printf 'dtc-revision: %s\n' "$dtc_revision"
  printf 'dtc-tree: %s\n' "$dtc_tree"
  printf 'keycodemapdb-repository: %s\n' "$keymap_repository"
  printf 'keycodemapdb-revision: %s\n' "$keymap_revision"
  printf 'keycodemapdb-tree: %s\n' "$keymap_tree"
  printf 'berkeley-softfloat-3-revision: %s\n' "$softfloat_revision"
  printf 'berkeley-softfloat-3-tree: %s\n' "$softfloat_tree"
  printf 'berkeley-testfloat-3-revision: %s\n' "$testfloat_revision"
  printf 'berkeley-testfloat-3-tree: %s\n' "$testfloat_tree"
  printf 'configure: %s\n' "$configure_command"
  printf 'build: %s\n' "$build_command"
} > "$output/BUILD_COMMANDS.txt"
printf '[]\n' > "$output/PATCHES.json"
(
  cd "$output"
  sha256sum \
    qemu-system-x86_64.js \
    qemu-system-x86_64.wasm \
    qemu-system-x86_64.worker.js \
    TOOLCHAIN.txt \
    BUILD_COMMANDS.txt \
    PATCHES.json > SHA256SUMS
)

observed="$(find "$output" -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | sort)"
expected="$(jq -r '.outputs[].path' "$manifest" | sort)"
if [[ "$observed" != "$expected" ]]; then
  echo "error: output inventory differs from manifest" >&2
  diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$observed") >&2 || true
  exit 1
fi

"$repo_root/scripts/verify-qemu-wasm-manifest.py" \
  --prototype --staging "$output"
"$repo_root/scripts/verify-qemu-wasm-manifest.py" \
  --evidence --staging "$output"

echo "source-built provisional qemu-wasm outputs in ${output#$repo_root/}"
