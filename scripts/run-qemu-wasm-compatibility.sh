#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"

demo="${LEANOS_QEMU_WASM_DEMO:-}"
[[ -n "$demo" ]] || {
  echo "error: set LEANOS_QEMU_WASM_DEMO to the pinned qemu-wasm-demo checkout" >&2
  exit 1
}
demo="$(cd "$demo" && pwd)"
images="$demo/docs/images"
runtime="$images/alpine-x86_64"
artifact="${LEANOS_QEMU_WASM_ARTIFACT_DIR:-build/qemu-wasm-compatibility}"
site="$artifact/site"
version="${LEANOS_VERSION:-0.1.0}"
iso="build/boot/leanos-${version}-x86_64.iso"
serial="$artifact/native.serial"
result="$artifact/browser-result.json"

for tool in git node npm python3 sha256sum curl google-chrome; do
  command -v "$tool" >/dev/null || { echo "error: missing required tool '$tool'" >&2; exit 1; }
done
[[ "$(git -C "$demo" rev-parse HEAD)" == 0208c86ea45253c26c0ea6907f6db2dec89eb7b2 ]]
[[ "$(git -C "$images" rev-parse HEAD)" == b7c549b5e6f4c376f76483a03e983214421434ad ]]
[[ "$(node --version)" == v24.18.0 ]]
[[ "$(npm --version)" == 11.16.0 ]]
[[ "$(google-chrome --version)" == "Google Chrome 150.0.7871.128" ]]

(
  cd "$runtime"
  sha256sum --check --strict <<'EOF'
15de099e1363ceb13a31b9d11836337bab974f9460836449330b20c0534d06c9  load-rom.data
617e4dc685cb2cedada4844f097eb18a56cf0f8bbd4c4e2e9231b4f07d0d8a88  load-rom.js
dab94140dc2ea847181ba47ae4cbd759728e551d8fd9ba9de409711ed25eddcc  out.js
f53107a35029d676aa551cd00d042f4f65af39a89bf72464494321fafdf54191  qemu-system-x86_64.wasm
8efab02a9cb5ee63ced22e9853bce74cbb895d15a5fb3d5139fef855c50f62ea  qemu-system-x86_64.worker.js
EOF
)
printf '%s  %s\n' \
  0ddfdc89547da3e9aaba7f39494f8c5358340d457d32c268fb9d7c793a3ca808 \
  "$demo/docs/coi-serviceworker.js" | sha256sum --check --strict

if [[ "${LEANOS_QEMU_WASM_SKIP_BUILD:-0}" == 1 ]]; then
  [[ -f "$iso" ]] || { echo "error: skipped build but '$iso' is absent" >&2; exit 1; }
else
  ./scripts/build-image.sh
fi
mkdir -p "$artifact" "$site"
LEANOS_SERIAL_LOG="$serial" ./scripts/run-image.sh "$iso" \
  >"$artifact/native.stdout" 2>"$artifact/native.stderr"
[[ "$(wc -c < "$iso")" -eq 14749696 ]]

cp "$runtime"/{load-rom.data,load-rom.js,out.js,qemu-system-x86_64.wasm,qemu-system-x86_64.worker.js} "$site/"
cp "$demo/docs/coi-serviceworker.js" "$site/"
cp scripts/qemu-wasm/{index.html,module.js,probe.mjs} "$site/"
cp docs/evidence/qemu-wasm-feasibility/{package.json,package-lock.json} "$site/"
cp "$iso" "$site/leanos.iso"
curl --fail --location --proto '=https' \
  https://unpkg.com/xterm@5.3.0/lib/xterm.js --output "$site/xterm.js"
curl --fail --location --proto '=https' \
  https://unpkg.com/xterm-pty@0.12.0/index.js --output "$site/xterm-pty.js"
(
  cd "$site"
  printf '%s  %s\n' \
    f0aea0f75f48559013ae6643c2479dd737d26da42d5524e6d2b70915ae6523c7 xterm.js \
    2e7cbffea02dad1f72637c564534d104a13f9eec306deb9cc34fffe1faa58947 xterm-pty.js |
    sha256sum --check --strict
  npm ci --ignore-scripts
)
cat "$site/leanos.iso" >> "$site/load-rom.data"
python3 - "$site/load-rom.js" docs/evidence/qemu-wasm-feasibility/load-rom-metadata.json <<'PY'
import json
import pathlib
import re
import sys
script = pathlib.Path(sys.argv[1])
metadata = json.loads(pathlib.Path(sys.argv[2]).read_text(encoding="utf-8"))
text, count = re.subn(
    r"loadPackage\(\{\"files\":.*?\}\);",
    "loadPackage(" + json.dumps(metadata, separators=(",", ":")) + ");",
    script.read_text(encoding="utf-8"),
)
if count != 1:
    raise SystemExit(f"expected one preload manifest, replaced {count}")
script.write_text(text, encoding="utf-8")
PY
[[ "$(wc -c < "$site/load-rom.data")" -eq 15222784 ]]

cat >"$artifact/metadata.txt" <<EOF
leanos_revision=$(git rev-parse HEAD)
iso_sha256=$(sha256sum "$iso" | cut -d' ' -f1)
qemu_wasm_demo_revision=0208c86ea45253c26c0ea6907f6db2dec89eb7b2
qemu_wasm_images_revision=b7c549b5e6f4c376f76483a03e983214421434ad
qemu_wasm_sha256=f53107a35029d676aa551cd00d042f4f65af39a89bf72464494321fafdf54191
browser=$(google-chrome --version)
node=$(node --version)
media=cdrom:/leanos.iso
machine=q35
cpu=max
vcpus=1
memory_mib=128
network=none
timeout_ms=${LEANOS_QEMU_WASM_TIMEOUT_MS:-180000}
EOF

(cd "$site" && python3 -m http.server 8765) >"$artifact/server.log" 2>&1 &
server_pid=$!
trap 'kill "$server_pid" 2>/dev/null || true' EXIT
start="$(date +%s)"
probe_status=0
set +e
(cd "$site" && node probe.mjs "../browser-result.json") \
  >"$artifact/browser.stdout" 2>"$artifact/browser.stderr"
probe_status=$?
set -e
elapsed="$(( $(date +%s) - start ))"
printf 'elapsed_seconds=%s\nprobe_process_status=%s\n' "$elapsed" "$probe_status" \
  >>"$artifact/metadata.txt"
kill "$server_pid" 2>/dev/null || true
wait "$server_pid" 2>/dev/null || true
trap - EXIT
[[ -f "$result" ]] || {
  echo "outcome=FAIL failure_class=browser-setup detail=probe-produced-no-result" |
    tee "$artifact/verdict.txt"
  exit 1
}
./scripts/check-qemu-wasm-result.py "$result" "$serial" |
  tee "$artifact/verdict.txt"
