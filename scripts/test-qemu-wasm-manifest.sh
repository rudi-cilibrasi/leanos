#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
validator="$repo_root/scripts/verify-qemu-wasm-manifest.py"
manifest="$repo_root/browser-runtime/manifest-v1.json"
fixtures="$(mktemp -d)"
trap 'rm -rf "$fixtures"' EXIT

"$validator" --inputs
"$validator" --evidence

write_prototype() {
  local output="$1"
  mkdir -p "$output"
  printf 'synthetic JavaScript glue\n' > "$output/qemu-system-x86_64.js"
  printf 'synthetic WebAssembly module\n' > "$output/qemu-system-x86_64.wasm"
  printf 'synthetic worker glue\n' > "$output/qemu-system-x86_64.worker.js"
  {
    printf 'container-image-id: synthetic\n'
    printf 'emcc (Emscripten gcc/clang-like replacement + linker emulating GNU ld) 3.1.50 (047b82506d6b471873300a5e4d1e690420b582d0)\n'
  } > "$output/TOOLCHAIN.txt"
  {
    printf 'manifest-sha256: %s\n' "$(sha256sum "$manifest" | cut -d ' ' -f 1)"
    printf 'configure: %s\n' "$(jq -r '.configuration.configure_command' "$manifest")"
    printf 'build: %s\n' "$(jq -r '.configuration.build_command' "$manifest")"
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
}

expect_rejection() {
  local name="$1"
  local expected="$2"
  if "$validator" --inputs --manifest "$fixtures/$name.json" \
      >"$fixtures/$name.out" 2>"$fixtures/$name.err"; then
    echo "error: fixture $name unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$fixtures/$name.err" || {
    echo "error: fixture $name failed for the wrong reason" >&2
    cat "$fixtures/$name.err" >&2
    exit 1
  }
}

jq '.toolchain.container.digest = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"' \
  "$manifest" > "$fixtures/substituted-container.json"
expect_rejection substituted-container "Dockerfile base does not match"

jq '.dependencies[0].sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"' \
  "$manifest" > "$fixtures/substituted-dependency.json"
expect_rejection substituted-dependency "Dockerfile does not enforce zlib"

jq '.patches = [{"path":"local.patch","sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","upstream_status":"not-submitted"}]' \
  "$manifest" > "$fixtures/undeclared-patch.json"
expect_rejection undeclared-patch "patch file is missing"

jq 'del(.licenses[] | select(.component == "qemu-wasm"))' \
  "$manifest" > "$fixtures/missing-license.json"
expect_rejection missing-license "license inventory is incomplete"

jq 'del(.outputs[] | select(.path == "qemu-system-x86_64.wasm"))' \
  "$manifest" > "$fixtures/missing-wasm.json"
expect_rejection missing-wasm "prototype output inventory is incomplete"

prototype="$fixtures/prototype"
write_prototype "$prototype"
"$validator" --prototype --staging "$prototype"

cp -a "$prototype" "$fixtures/substituted-wasm"
printf 'substitution\n' >> "$fixtures/substituted-wasm/qemu-system-x86_64.wasm"
if "$validator" --prototype --staging "$fixtures/substituted-wasm" \
    >"$fixtures/substituted-wasm.out" 2>"$fixtures/substituted-wasm.err"; then
  echo "error: substituted Wasm fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq "prototype output differs from SHA256SUMS" \
  "$fixtures/substituted-wasm.err"

cp -a "$prototype" "$fixtures/missing-runtime-output"
rm "$fixtures/missing-runtime-output/qemu-system-x86_64.worker.js"
if "$validator" --prototype --staging "$fixtures/missing-runtime-output" \
    >"$fixtures/missing-runtime-output.out" \
    2>"$fixtures/missing-runtime-output.err"; then
  echo "error: missing runtime output fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq "prototype inventory differs from manifest" \
  "$fixtures/missing-runtime-output.err"

cp -a "$prototype" "$fixtures/changed-js"
printf 'reviewed change\n' >> "$fixtures/changed-js/qemu-system-x86_64.js"
(
  cd "$fixtures/changed-js"
  sha256sum \
    qemu-system-x86_64.js \
    qemu-system-x86_64.wasm \
    qemu-system-x86_64.worker.js \
    TOOLCHAIN.txt \
    BUILD_COMMANDS.txt \
    PATCHES.json > SHA256SUMS
)
"$validator" --prototype --staging "$fixtures/changed-js"
if "$validator" --prototype --staging "$prototype" \
    --compare "$fixtures/changed-js" \
    >"$fixtures/changed-js.out" 2>"$fixtures/changed-js.err"; then
  echo "error: divergent clean-build fixture unexpectedly passed" >&2
  exit 1
fi
grep -Fq "clean builds are not byte-identical: qemu-system-x86_64.js" \
  "$fixtures/changed-js.err"

if "$validator" --release --manifest "$manifest" \
    >"$fixtures/release.out" 2>"$fixtures/release.err"; then
  echo "error: provisional manifest unexpectedly passed release validation" >&2
  exit 1
fi
grep -Fq "acceptance.ready is not true" "$fixtures/release.err"

echo "qemu-wasm manifest, prototype integrity, and negative fixtures passed"
