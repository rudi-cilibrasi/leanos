# ADR 0011: Defer a qemu-wasm demo pending a bootable media path

- Status: Accepted
- Date: 2026-07-27
- Issue: [#178](https://github.com/rudi-cilibrasi/leanos/issues/178)
- Spike verdict: **PARTIAL**

## Decision

Do not yet describe a LeanOS qemu-wasm GitHub Pages demo as feasible.  A
bounded probe established that the upstream x86-64 WebAssembly build starts in
a browser, reaches SeaBIOS, and can expose its terminal through a pseudo-TTY.
It did not boot the tested LeanOS ISO through either an IDE disk or CD-ROM
within 180 seconds.  This is useful platform evidence, but not a LeanOS boot.

Implementation may proceed after one of these media gates is closed:

1. a pinned qemu-wasm build boots the unchanged LeanOS ISO with the existing
   `q35` device contract; or
2. a different browser-visible boot device is deliberately added to the
   LeanOS device model, DMA quarantine, image policy, and exact boot evidence.

The second option is architecture and security-claim work, not demo
packaging.  In particular, silently adding `virtio-blk-pci` is rejected:
native QEMU reaches LeanOS with that device but the guest correctly emits
`FINAL status=FAIL reason=dma-inventory`.

If the first gate can be closed without a qemu-wasm fork, estimate **6--10
engineering days** for a reviewable demo: 2--3 days to make and test the
browser boot path, 1--2 days to vendor the terminal/runtime assets and handle
cross-origin isolation, 1--2 days for a reproducible Pages build and licenses,
and 2--3 days for browser fixtures, documentation, and CI.  Maintaining a
qemu-wasm fork or expanding LeanOS's device model is unestimated until the
media failure is diagnosed; either can exceed that range.

## Conditional implementation steps

The 6--10 day implementation starts only after the unchanged ISO boots through
a pinned, unforked qemu-wasm build and produces the complete LeanOS protocol
plus debug-exit status 33.  Diagnosing and closing that media gate is not part
of the estimate.  Once it is closed:

1. Add a repository-owned script that builds the existing ISO, verifies its
   hash, copies the pinned qemu-wasm runtime and firmware into a staging
   directory, and generates the Emscripten preload manifest containing
   `/leanos.iso`.  Pin every upstream revision and tool version; fail on an
   unexpected input hash.
2. Add a minimal static browser entry point that starts
   `qemu-system-x86_64.wasm` with the accepted media mapping and the exact
   `q35`, memory, CPU, no-network, serial, and debug-exit arguments.  Connect
   the pseudo-TTY to the terminal, surface startup failures, and install the
   cross-origin-isolation service worker required by the threaded runtime.
3. Add one repository-owned browser test command that serves the staged site,
   waits through the service-worker reload, requires
   `crossOriginIsolated=true`, and boots under a fixed timeout.  It must capture
   the console and pass only on both the complete exact LeanOS protocol and
   debug-exit status 33; add negative fixtures for missing preload data,
   truncated protocol, guest failure, and timeout.
4. Add a Pages build workflow that invokes only the repository-owned staging
   and browser-test commands, uploads the tested staging directory unchanged,
   and deploys that artifact.  Pin actions, set least-privilege permissions,
   enforce Pages and repository object-size limits, and keep deployment
   separate from pull-request validation.
5. Inventory and preserve license notices for QEMU, firmware, Emscripten
   runtime, terminal, and service-worker assets.  Document the pinned versions,
   local reproduction command, browser support boundary, download size,
   isolation requirement, cache/service-worker recovery, and the distinction
   between emulator-tested behavior and proved LeanOS claims.
6. Run the browser fixture in the supported desktop browser matrix on pull
   requests, then perform first-load, cached-load, keyboard, accessibility, and
   deployed-Pages smoke checks before enabling the public demo link.

## Tested facts

The probe used LeanOS revision
`b5bb7fea627972dfbe682f777466af8a715f7cd8`, qemu-wasm source revision
`0ef7b4e2814b231705d8371dd7997f5b72e70baf` (`VERSION` is `8.2.0`),
qemu-wasm-demo revision `0208c86ea45253c26c0ea6907f6db2dec89eb7b2`,
and its images submodule revision
`b7c549b5e6f4c376f76483a03e983214421434ad`.  The source Dockerfile pins
Emscripten SDK 3.1.50.  The prebuilt WebAssembly artifact was tested, rather
than claiming that it was reproduced from those sources.

The host was Ubuntu 24.04 x86-64.  Native control runs used QEMU 8.2.2
(`1:8.2.2+ds-0ubuntu1.17`).  Browser runs used Google Chrome
150.0.7871.128, Node.js 24.18.0, and `puppeteer-core` 24.16.0.  The browser
reported `crossOriginIsolated=true`.

The unchanged 14,749,696-byte ISO had SHA-256
`097914961a25ad1e2970c07b76ca58752779739e1e96213b97014c3cdd75e1a9`.
`./scripts/run-image.sh` booted that ISO natively using `-cdrom`, observed the
complete exact LeanOS protocol and guest-success status 33, and completed in
1.33 seconds with 81,452 KiB maximum host RSS.

The prebuilt `qemu-system-x86_64.wasm` was 40,799,480 bytes, had SHA-256
`f53107a35029d676aa551cd00d042f4f65af39a89bf72464494321fafdf54191`,
and compressed to 14,389,952 bytes with `gzip -9`.  The ISO compressed to
4,631,518 bytes.  These measurements show that the two largest required
artifacts fit below GitHub's 100 MiB per-file repository limit; they do not
measure a deployed site's bandwidth or startup latency.

For browser tests, the exact ISO bytes were appended to the upstream
`load-rom.data` preload and, importantly, also registered in
`load-rom.js` as:

```json
{"filename":"/leanos.iso","start":473088,"end":15222784}
```

The preload's `remote_package_size` was changed to `15222784`.  Without both
changes, `/leanos.iso` does not exist in Emscripten's filesystem and a media
failure says nothing about LeanOS compatibility.

The common qemu-wasm arguments were:

```text
-nographic -machine q35 -cpu max -smp 1 -m 128M
-accel tcg,tb-size=500 -L /pack-rom -monitor none -nic none
-no-reboot -no-shutdown
-device isa-debug-exit,iobase=0xf4,iosize=0x04
```

With `-drive file=/leanos.iso,format=raw,if=ide`, the bounded run completed
without a LeanOS record:

```text
SeaBIOS (version rel-1.16.3-0-ga6ed6b701f0a-prebuilt.qemu.org)
Booting from Hard Disk...
Boot failed: could not read the boot disk
Booting from DVD/CD...
Boot failed: Could not read from CDROM (code 0003)
Booting from Floppy...
Boot failed: could not read the boot disk
No bootable device
```

Chrome elapsed time was 62.69 seconds with 211,624 KiB maximum RSS; the
automation's observation bound was 60 seconds.

With `-cdrom /leanos.iso`, the same final firmware transcript was observed
after a 180-second bound.  Chrome elapsed time was 181.57 seconds with 229,312
KiB maximum RSS.  This invalidates neither QEMU's general browser feasibility
nor LeanOS's ISO: it only establishes that this pinned prebuilt combination
did not provide a working optical boot in the tested bound.

The upstream x86-64 demo uses a VirtIO block device.  A native control using
the same proposed mapping was:

```sh
timeout 30 qemu-system-x86_64 \
  -machine q35,accel=tcg -cpu max -smp 1 -m 128M \
  -display none -monitor none -serial file:/tmp/leanos-virtio.log \
  -no-reboot -no-shutdown -nic none \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -drive id=leanos,file=build/boot/leanos-0.1.0-x86_64.iso,format=raw,if=none \
  -device virtio-blk-pci,drive=leanos -boot c
```

It returned guest-error status 35 and logged:

```text
LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap
LEANOS/3 FINAL status=FAIL reason=dma-inventory
```

That is a successful security boundary, not a browser-demo success.

## Reproduction boundary

The exact browser module variants, HTML, Puppeteer harness, preload metadata,
preparation commands, input hashes, observation bounds, and retained output
are checked in under
[`docs/evidence/qemu-wasm-feasibility/`](../evidence/qemu-wasm-feasibility/README.md).
That evidence bundle preserves the probe-specific replacement for the
upstream `pc`, kernel/initrd, VirtIO, networking, and hard-coded demo-path
configuration.

Keep this evidence-bearing checkout at the revision containing this ADR and
build the pinned native control in a separate detached worktree.  Copy the
verified ISO back before preparing the browser probe:

```sh
set -eu
native_parent="$(mktemp -d)"
native_worktree="$native_parent/leanos-b5bb7fe"
git worktree add --detach "$native_worktree" \
  b5bb7fea627972dfbe682f777466af8a715f7cd8
(
  cd "$native_worktree"
  ./scripts/build-image.sh
  ./scripts/run-image.sh
  printf '%s  %s\n' \
    097914961a25ad1e2970c07b76ca58752779739e1e96213b97014c3cdd75e1a9 \
    build/boot/leanos-0.1.0-x86_64.iso |
    sha256sum --check --strict
)
mkdir -p build/boot
cp "$native_worktree/build/boot/leanos-0.1.0-x86_64.iso" build/boot/
git worktree remove --force "$native_worktree"
rmdir "$native_parent"
```

Fetch the exact upstream inputs:

```sh
git clone https://github.com/ktock/qemu-wasm.git
git -C qemu-wasm checkout 0ef7b4e2814b231705d8371dd7997f5b72e70baf
git clone https://github.com/ktock/qemu-wasm-demo.git
git -C qemu-wasm-demo checkout 0208c86ea45253c26c0ea6907f6db2dec89eb7b2
git -C qemu-wasm-demo submodule update --init
test "$(git -C qemu-wasm-demo/docs/images rev-parse HEAD)" = \
  b7c549b5e6f4c376f76483a03e983214421434ad
```

Use the x86-64 files under
`qemu-wasm-demo/docs/images/alpine-x86_64/`, append the ISO to a copy of
`load-rom.data`, and add the preload mapping shown above.  Serve the site over
HTTP with the demo's `coi-serviceworker.js`; wait for its first-load reload and
require `crossOriginIsolated=true`.  Run each media form with the common
arguments above, capture the pseudo-TTY, and accept a LeanOS result only if the
exact repository protocol and debug-exit status 33 both occur.  A firmware
banner, timeout, or partial protocol is not acceptance evidence.

The commands pin the sources inspected and the prebuilt artifacts tested.
They do not prove that the images submodule was produced from the inspected
qemu-wasm commit.  Closing that provenance gap requires rebuilding the
WebAssembly artifact with Emscripten 3.1.50 and recording its complete tool
inventory and hashes.

## Unknowns

- The cause of the IDE/CD-ROM read failure is unknown.  It may be a disabled or
  incomplete block backend, an Emscripten file-I/O integration defect, or a
  qemu-wasm-specific device issue.
- No Firefox, Safari, mobile, low-memory, cached/offline, keyboard-input, or
  accessibility test was run.
- The probe used a local static server, not GitHub Pages.  The copied
  cross-origin-isolation service worker worked in Chrome, but Pages deployment,
  cache invalidation, CSP, and service-worker upgrades remain untested.
- Runtime and firmware redistribution obligations have not received a release
  review.  QEMU states GPLv2 for the emulator as a whole and separately
  licensed bundled firmware must be inventoried.
- Startup transfer and execution time on typical client hardware are unknown.
  Local byte sizes and host RSS are not user-facing performance measurements.

## Trusted assumptions and claim limit

The browser, JavaScript engine, WebAssembly implementation, `SharedArrayBuffer`
and service-worker isolation behavior, Emscripten runtime, qemu-wasm/QEMU TCG,
SeaBIOS, xterm pseudo-TTY bridge, preload generator, and browser automation are
trusted.  The source-to-prebuilt-artifact correspondence is also trusted until
the artifact is rebuilt.

GitHub documents a 1 GiB published-site limit, a recommended 1 GiB source
repository limit, and a soft 100 GiB monthly bandwidth limit:
<https://docs.github.com/en/pages/getting-started-with-github-pages/github-pages-limits>.
GitHub also enforces a 100 MiB single-object limit in normal Git repositories:
<https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-large-files-on-github>.
Those published limits and the measured files make Pages capacity plausible,
not validated.  Emscripten documents that pthreads require
`SharedArrayBuffer` and cross-origin isolation:
<https://emscripten.org/docs/porting/pthreads.html>.

This ADR is feasibility evidence and a workload boundary.  It proves no
LeanOS property, no model-to-binary refinement, no browser or emulator
correctness, and no GitHub Pages deployment.  The strongest tested claim is
that a pinned qemu-wasm prebuilt reaches firmware in one Chrome environment
but does not boot the unchanged LeanOS image through the tested IDE or CD-ROM
paths within the stated bounds.
