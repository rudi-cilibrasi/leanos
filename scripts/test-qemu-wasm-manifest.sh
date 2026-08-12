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

jq '.toolchain.apt_snapshot.timestamp = "20250602T000000Z"' \
  "$manifest" > "$fixtures/changed-apt-snapshot.json"
expect_rejection changed-apt-snapshot \
  "APT snapshot identity differs from the reviewed immutable input"

jq '.configuration.configure_command += " --enable-slirp"' \
  "$manifest" > "$fixtures/divergent-configure-command.json"
expect_rejection divergent-configure-command \
  "configure command differs from its argument inventory"

jq '.configuration.configure_arguments += ["--enable-slirp;touch /tmp/escaped"]' \
  "$manifest" > "$fixtures/unsafe-configure-argument.json"
expect_rejection unsafe-configure-argument \
  "configure argument inventory contains an unsafe argument"

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

cp -a "$prototype" "$fixtures/prototype-directory-entry"
mkdir "$fixtures/prototype-directory-entry/unmanifested"
if "$validator" --prototype --staging "$fixtures/prototype-directory-entry" \
    >"$fixtures/prototype-directory-entry.out" \
    2>"$fixtures/prototype-directory-entry.err"; then
  echo "error: prototype directory entry unexpectedly passed" >&2
  exit 1
fi
grep -Fq "staging contains non-regular entries" \
  "$fixtures/prototype-directory-entry.err"

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

release_staging="$fixtures/release-staging"
mkdir "$release_staging"
release_outputs='[
  {"path":"qemu-system-x86_64.wasm","asset_class":"wasm"},
  {"path":"qemu-system-x86_64.js","asset_class":"javascript-glue"},
  {"path":"qemu-system-x86_64.worker.js","asset_class":"worker"},
  {"path":"firmware.bin","asset_class":"firmware"},
  {"path":"terminal.js","asset_class":"terminal"},
  {"path":"coi-serviceworker.js","asset_class":"service-worker"},
  {"path":"leanos.data","asset_class":"preload"},
  {"path":"index.html","asset_class":"browser-harness"},
  {"path":"LICENSES.txt","asset_class":"license-bundle"},
  {"path":"BUILD.log","asset_class":"build-log"},
  {"path":"TOOLCHAIN.txt","asset_class":"tool-versions"},
  {"path":"PATCHES.json","asset_class":"patch-inventory"},
  {"path":"browser-evidence.json","asset_class":"browser-evidence"}
]'
jq -r '.[].path' <<<"$release_outputs" |
  while IFS= read -r path; do
    printf 'synthetic release fixture: %s\n' "$path" > "$release_staging/$path"
  done
release_manifest="$fixtures/release-manifest.json"
jq --argjson outputs "$release_outputs" '
  .acceptance.ready = true
  | del(.acceptance.pending_gate, .acceptance.provisional_reason)
  | .deferred_outputs = []
  | .outputs = ($outputs | map(
      . + {
        role: ("synthetic " + .asset_class + " fixture"),
        sha256: null,
        size: null
      }
    ))
' "$manifest" > "$release_manifest.unhashed"
python3 - "$release_manifest.unhashed" "$release_manifest" "$release_staging" <<'PY'
import hashlib
import json
import pathlib
import sys

source, destination, staging = map(pathlib.Path, sys.argv[1:])
manifest = json.loads(source.read_text())
for output in manifest["outputs"]:
    artifact = staging / output["path"]
    output["sha256"] = hashlib.sha256(artifact.read_bytes()).hexdigest()
    output["size"] = artifact.stat().st_size
destination.write_text(json.dumps(manifest, indent=2) + "\n")
PY
"$validator" --release --manifest "$release_manifest" --staging "$release_staging"

expect_release_rejection() {
  local name="$1"
  local expected="$2"
  local fixture_staging="$fixtures/$name"
  shift 2
  cp -a "$release_staging" "$fixture_staging"
  "$@" "$fixture_staging"
  if "$validator" --release --manifest "$release_manifest" \
      --staging "$fixture_staging" \
      >"$fixtures/$name.out" 2>"$fixtures/$name.err"; then
    echo "error: release fixture $name unexpectedly passed" >&2
    exit 1
  fi
  grep -Fq "$expected" "$fixtures/$name.err" || {
    echo "error: release fixture $name failed for the wrong reason" >&2
    cat "$fixtures/$name.err" >&2
    exit 1
  }
}

remove_firmware() {
  rm "$1/firmware.bin"
}
expect_release_rejection missing-firmware \
  "staging inventory differs from manifest" remove_firmware

remove_license_bundle() {
  rm "$1/LICENSES.txt"
}
expect_release_rejection missing-license-material \
  "staging inventory differs from manifest" remove_license_bundle

substitute_wasm() {
  printf 'substituted module\n' >> "$1/qemu-system-x86_64.wasm"
}
expect_release_rejection substituted-release-wasm \
  "staged output differs from manifest: qemu-system-x86_64.wasm" substitute_wasm

change_javascript() {
  printf 'changed glue\n' >> "$1/qemu-system-x86_64.js"
}
expect_release_rejection changed-release-javascript \
  "staged output differs from manifest: qemu-system-x86_64.js" change_javascript

add_unmanifested_staging_file() {
  printf 'unmanifested\n' > "$1/extra.js"
}
expect_release_rejection divergent-release-staging \
  "staging inventory differs from manifest" add_unmanifested_staging_file

add_symlinked_staging_entry() {
  ln -s qemu-system-x86_64.wasm "$1/runtime-alias.wasm"
}
expect_release_rejection symlinked-release-staging \
  "staging contains non-regular entries" add_symlinked_staging_entry

jq 'del(.outputs[] | select(.asset_class == "firmware"))' \
  "$release_manifest" > "$fixtures/release-missing-firmware-class.json"
if "$validator" --release \
    --manifest "$fixtures/release-missing-firmware-class.json" \
    >"$fixtures/release-missing-firmware-class.out" \
    2>"$fixtures/release-missing-firmware-class.err"; then
  echo "error: release manifest without firmware unexpectedly passed" >&2
  exit 1
fi
grep -Fq "release output asset classes are incomplete" \
  "$fixtures/release-missing-firmware-class.err"

jq 'del(.outputs[] | select(.asset_class == "license-bundle"))' \
  "$release_manifest" > "$fixtures/release-missing-license-class.json"
if "$validator" --release \
    --manifest "$fixtures/release-missing-license-class.json" \
    >"$fixtures/release-missing-license-class.out" \
    2>"$fixtures/release-missing-license-class.err"; then
  echo "error: release manifest without license bundle unexpectedly passed" >&2
  exit 1
fi
grep -Fq "release output asset classes are incomplete" \
  "$fixtures/release-missing-license-class.err"

echo "qemu-wasm manifest, prototype integrity, and negative fixtures passed"
