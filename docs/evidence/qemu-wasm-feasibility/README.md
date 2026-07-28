# qemu-wasm feasibility probe

This directory preserves the browser-side changes used for ADR 0011.  The
files are evidence for a bounded feasibility probe, not a supported demo.

Pinned inputs:

- qemu-wasm-demo: `0208c86ea45253c26c0ea6907f6db2dec89eb7b2`
- images submodule: `b7c549b5e6f4c376f76483a03e983214421434ad`
- LeanOS ISO SHA-256:
  `097914961a25ad1e2970c07b76ca58752779739e1e96213b97014c3cdd75e1a9`
- qemu-system-x86_64.wasm SHA-256:
  `f53107a35029d676aa551cd00d042f4f65af39a89bf72464494321fafdf54191`
- browser terminal dependencies:
  - `xterm` 5.3.0 SHA-256:
    `f0aea0f75f48559013ae6643c2479dd737d26da42d5524e6d2b70915ae6523c7`
  - `xterm-pty` 0.12.0 SHA-256:
    `2e7cbffea02dad1f72637c564534d104a13f9eec306deb9cc34fffe1faa58947`
- Chrome 150.0.7871.128, Node.js 24.18.0, and
  npm 11.16.0
- `puppeteer-core` 24.16.0 and its complete transitive dependency graph,
  pinned by the checked-in `package-lock.json`

First follow ADR 0011's separate-worktree native-control commands.  They leave
the evidence-bearing LeanOS checkout unchanged and copy the hash-verified
pinned ISO to `build/boot/leanos-0.1.0-x86_64.iso`.  From that checkout and a
clean checkout of the pinned demo, prepare the probe as follows.  The upstream
`coi-serviceworker.js`, WebAssembly, worker, `out.js`, and firmware preload
remain unchanged.

```sh
probe=build/qemu-wasm-probe
image=qemu-wasm-demo/docs/images/alpine-x86_64
mkdir -p "$probe"
cp "$image"/{coi-serviceworker.js,load-rom.data,load-rom.js,out.js,qemu-system-x86_64.wasm,qemu-system-x86_64.worker.js} "$probe"/
cp build/boot/leanos-0.1.0-x86_64.iso "$probe/leanos.iso"
cp docs/evidence/qemu-wasm-feasibility/{index.html,module-cdrom.js,probe.mjs,package.json,package-lock.json} "$probe"/
cp "$probe/module-cdrom.js" "$probe/module.js"
curl --fail --location --proto '=https' \
  https://unpkg.com/xterm@5.3.0/lib/xterm.js \
  --output "$probe/xterm.js"
curl --fail --location --proto '=https' \
  https://unpkg.com/xterm-pty@0.12.0/index.js \
  --output "$probe/xterm-pty.js"
(
  cd "$probe"
  printf '%s  %s\n' \
    f0aea0f75f48559013ae6643c2479dd737d26da42d5524e6d2b70915ae6523c7 \
    xterm.js \
    2e7cbffea02dad1f72637c564534d104a13f9eec306deb9cc34fffe1faa58947 \
    xterm-pty.js |
    sha256sum --check --strict
)
test "$(wc -c < "$probe/load-rom.data")" -eq 473088
cat "$probe/leanos.iso" >> "$probe/load-rom.data"
python3 - "$probe/load-rom.js" docs/evidence/qemu-wasm-feasibility/load-rom-metadata.json <<'PY'
import json
import pathlib
import re
import sys

script = pathlib.Path(sys.argv[1])
metadata = json.loads(pathlib.Path(sys.argv[2]).read_text())
text = script.read_text()
replacement = "loadPackage(" + json.dumps(metadata, separators=(",", ":")) + ");"
text, count = re.subn(r"loadPackage\(\{\"files\":.*?\}\);", replacement, text)
if count != 1:
    raise SystemExit(f"expected one preload manifest, replaced {count}")
script.write_text(text)
PY
sha256sum "$probe/leanos.iso" "$probe/qemu-system-x86_64.wasm"
test "$(wc -c < "$probe/load-rom.data")" -eq 15222784
test "$(node --version)" = v24.18.0
test "$(npm --version)" = 11.16.0
test "$(/usr/bin/google-chrome --version)" = \
  "Google Chrome 150.0.7871.128 "
(cd "$probe" && npm ci --ignore-scripts)
```

Run the CD-ROM observation with the exact 180-second browser bound:

```sh
(cd build/qemu-wasm-probe && python3 -m http.server 8765) &
server_pid=$!
/usr/bin/time -v timeout 190 node build/qemu-wasm-probe/probe.mjs
kill "$server_pid"
```

For the IDE observation, replace only the media arguments and bound:

```sh
cp docs/evidence/qemu-wasm-feasibility/module-ide.js \
  build/qemu-wasm-probe/module.js
sed 's/timeout: 180000/timeout: 60000/' \
  docs/evidence/qemu-wasm-feasibility/probe.mjs \
  > build/qemu-wasm-probe/probe-ide.mjs
(cd build/qemu-wasm-probe && python3 -m http.server 8765) &
server_pid=$!
/usr/bin/time -v timeout 70 node build/qemu-wasm-probe/probe-ide.mjs
kill "$server_pid"
```

`index.html` loads the cross-origin-isolation service worker before checking
`crossOriginIsolated`, imports only the locally served terminal dependencies
after their SHA-256 verification, connects the QEMU pseudo-TTY to xterm, and
exposes the captured terminal to Puppeteer.  `probe.mjs` records console and
page errors, waits for debug exit 33 or abort, and serializes the terminal.
The exact observed transcript and `/usr/bin/time -v` measurements are retained
in `retained-output.txt`.
