# LeanOS browser demo — third-party license inventory

The deployable demo site (`build/browser/site/`, issue #192) redistributes the
components below. Each is fetched at a pinned revision and hash-verified against
`scripts/browser-boot/manifest.json` before staging. LeanOS itself is licensed
under Apache-2.0 (see the repository `LICENSE`); the demo does not relicense it.

This inventory records redistribution obligations for the demo bundle. It is not
legal advice, and it does not extend any LeanOS proof or claim to the emulator,
firmware, browser, or terminal.

| Component | Source | License |
| --- | --- | --- |
| QEMU (`qemu-system-x86_64.wasm`) | ktock/qemu-wasm 8.2.0 (Emscripten build) | GPL-2.0-only |
| Emscripten loader/worker (`out.js`, `qemu-system-x86_64.worker.js`) | ktock/qemu-wasm-demo `0208c86` | GPL-2.0-only (generated) |
| Firmware preload (`load-rom.data`, `load-rom.js`) | QEMU bundled firmware (SeaBIOS + option ROMs) | SeaBIOS LGPL-3.0; bundled ROMs per QEMU firmware licenses |
| Cross-origin-isolation service worker (`coi-serviceworker.js`) | gzuidhof/coi-serviceworker | MIT |
| Terminal (`xterm.js`, `xterm.css`) | xtermjs/xterm.js 5.3.0 | MIT |
| Terminal pty bridge (`xterm-pty.js`) | mame/xterm-pty 0.12.0 | MIT |
| Demo page and module (`index.html`, `leanos-module.js`) | this repository | Apache-2.0 |
| LeanOS image (`leanos.iso`) | this repository | Apache-2.0 |

## Notes

- The QEMU WebAssembly artifact is the upstream prebuilt: it is tested here, not
  reproduced from source. Reproducible provenance for the emulator is tracked in
  issue #194.
- QEMU is GPL-2.0-only as a whole; the corresponding source is the pinned
  `ktock/qemu-wasm` revision recorded in `scripts/browser-boot/manifest.json`.
- The bundled firmware in `load-rom.data` is separately licensed from QEMU; its
  components follow the QEMU firmware license inventory.
