# In-browser boot compatibility (qemu-wasm)

This harness boots the **unchanged** canonical LeanOS ISO in a pinned, unforked
[qemu-wasm](https://github.com/ktock/qemu-wasm) WebAssembly runtime and requires
the same complete versioned serial protocol and guest debug-exit status 33 as
the native reference run. It closes media gate 1 of
[ADR 0011](adr/0011-qemu-wasm-feasibility.md) (issue #193). It is compatibility
evidence at an existing trusted boundary, not a proof: the browser, WebAssembly
engine, Emscripten runtime, qemu-wasm/QEMU TCG, SeaBIOS, and the prebuilt
artifact are all trusted.

## Why the ADR probe stalled, and what changed

The ADR 0011 feasibility probe reached SeaBIOS but never read the boot media
(`Boot failed: Could not read from CDROM (code 0003)`). Tracing the qemu-wasm
device layer showed the ATAPI/AHCI READ was issued and its asynchronous
completion callback never fired, followed by hundreds of thousands of idle
status polls; a Linux `-kernel` control on the same page panicked with
`IO-APIC + timer doesn't work`. Both are the same fault: QEMU's main event loop
was blocked inside Emscripten's TTY `poll` waiting on the xterm pseudo-terminal
stdin, which starves the timer and AIO-completion bottom halves the main loop
services. The upstream demo works around this with a post-init override of
`Module.TTY.stream_ops.poll`.

This harness sidesteps the pseudo-terminal entirely: it maps the canonical
`-serial file:` chardev to an in-memory (MEMFS) file. With no stdio chardev the
main loop never enters the blocking TTY poll, and the captured transcript is
**byte-identical to a native `-serial file:` run**, so the existing protocol
gate validates it unchanged.

## Design

`scripts/browser-boot/qemu-wasm-shim.mjs` is a QEMU-shaped shim invoked by the
unchanged `scripts/run-image.sh` through `LEANOS_QEMU`. It answers `--version`,
accepts the canonical `leanos_q35_command` argument vector, boots those exact
bytes in the pinned browser runtime, writes the guest serial to the requested
`-serial file:` target, and exits with the guest debug-exit status. The runner
then performs its normal canonical expected-protocol comparison, DMA quarantine
snapshot, and VT-d activation snapshot on the captured serial. Acceptance is
therefore the native acceptance path — there is no browser-only `PASS` string.

The only guest-visible change to the argument vector is redirecting the host
serial-log and ISO paths to fixed MEMFS paths and ensuring `-L /pack-rom/` (the
firmware search path the WebAssembly build needs) is present. The machine, CPU,
one-vCPU scope, memory, no-network policy, device topology (including the pinned
`intel-iommu`), and debug-exit device pass through verbatim. The ISO is injected
into MEMFS through an Emscripten `preRun` run-dependency, so the upstream
firmware preload is used unmodified rather than byte-patched.

## Running it

```sh
./scripts/build-image.sh                       # canonical ISO
./scripts/prepare-browser-runtime.sh           # fetch + hash-verify pinned runtime
npx --yes @puppeteer/browsers install chrome@stable --path build/browser/chrome
LEANOS_BROWSER=build/browser/chrome/chrome/linux-*/chrome-linux64/chrome \
  ./scripts/run-browser-boot.sh
```

`prepare-browser-runtime.sh` clones `ktock/qemu-wasm-demo` at the pinned
revision, verifies the images submodule commit, and checks every redistributed
asset against `scripts/browser-boot/manifest.json`; one hash mismatch aborts.
`run-browser-boot.sh` records `build/browser/browser-boot-<scenario>.json` with
the ISO SHA-256, qemu-wasm WebAssembly SHA-256, browser version, source
revision, elapsed time, and result.

Requires network access, a browser download, and cross-origin isolation, so it
is an on-demand command rather than a default CI gate. Reproducible runtime
provenance (issue #194) and GitHub Pages deployment (issue #192) build on this
gate and are out of scope here.

## Public demo (GitHub Pages)

The same pinned runtime backs an interactive public demo (issue #192).
`scripts/stage-browser-demo.sh` re-verifies every runtime asset against the
manifest and assembles a **self-contained** site in `build/browser/site/` —
the demo page (`scripts/browser-boot/demo/`), the pinned runtime and terminal
assets, the license inventory, and the unchanged ISO — with no remote runtime
dependencies. The demo page routes serial to a MEMFS file and tails it into an
xterm terminal, so a viewer watches the boot protocol live and sees
`guest exited (status 33)` on success.

`.github/workflows/pages.yml` builds the ISO, prepares and hash-verifies the
runtime, boots the staged site in a browser as the acceptance gate
(`scripts/run-browser-boot.sh`), and deploys the staged directory unchanged. It
runs only on the default branch and manual dispatch, separate from
pull-request validation, with pinned actions and least-privilege permissions.
Enabling Pages with source "GitHub Actions" is a one-time repository setting.
Third-party redistribution licenses are inventoried in
[browser-demo-licenses.md](browser-demo-licenses.md).

## Offline fixtures (gated by `check.sh`)

`scripts/test-browser-boot.sh` needs no browser or network. It unit-tests the
shim's argument translation and its runtime-outcome decision logic
(`scripts/browser-boot/evaluate.mjs`), then drives `scripts/run-image.sh` with a
mock emulator to prove a firmware-only transcript, a truncated protocol, an
empty-serial media failure, a guest failure status, a boot timeout, and a
runtime abort are each rejected — a firmware banner or partial LeanOS transcript
cannot be accepted as a boot.

## Trusted boundary

The prebuilt WebAssembly artifact is tested, not reproduced from source; that
correspondence is a trusted assumption until issue #194 rebuilds it. This
harness proves no LeanOS property, no model-to-binary refinement, and no browser
or emulator correctness — only that the pinned runtime boots the reviewed image
to the complete protocol and status 33.
