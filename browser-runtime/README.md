# qemu-wasm source-build contract

This directory is the issue #194 source-build lane.  It does not contain or
copy the upstream images submodule's prebuilt emulator.

`manifest-v1.json` is a versioned, machine-readable input lock for the
currently investigated ADR 0011 source revision.  Issue #193 must replace the
provisional qemu-wasm revision/configuration if its media investigation selects
another one.  Until that happens, the manifest deliberately has
`acceptance.ready: false`; no output hashes or LeanOS browser-boot claim may be
published from this prototype lock.

The build has two commands:

```sh
./scripts/verify-qemu-wasm-manifest.py --inputs
./scripts/build-qemu-wasm-source.sh
./scripts/reproduce-qemu-wasm-source.sh
```

The first command is cheap and fail-closed.  It checks the source/tree pins,
container identity, host platform, dependency download hashes, complete
configure/build commands, patch inventory, license inventory, declared output
set, and the explicit #193 blocker.  The second command fetches only the
recorded qemu-wasm commit, builds the repository-owned toolchain container, and
compiles the x86-64 system emulator from that checkout.  It never reads the
qemu-wasm-demo images submodule.

The third command performs the publication gate for the provisional output
set: it runs two isolated clean builds, validates each complete output
inventory against `SHA256SUMS`, and rejects any byte difference between the
two directories.

`provisional-source-build-evidence-v1.json` records the observed hashes and
sizes from two byte-identical clean builds of this provisional manifest.  It
is source-build evidence only: `acceptance_ready` remains false, and the file
does not claim the deferred firmware, browser staging, or LeanOS boot gate.

The container base is both versioned and digest-pinned for `linux/amd64`.
Every non-apt source archive is versioned and SHA-256 checked before use.
Top-level apt packages are exact-version requests; the build also records the
complete resulting `dpkg` inventory because transitive Ubuntu packages remain
an input supplied by the pinned base image's configured archive.  Two clean
builds and byte-identical output locking remain required before
`acceptance.ready` can become true.

Expected prototype outputs are:

- `qemu-system-x86_64.js` — Emscripten JavaScript launcher/glue;
- `qemu-system-x86_64.wasm` — source-built emulator module;
- `qemu-system-x86_64.worker.js` — pthread worker glue;
- `TOOLCHAIN.txt` — exact compiler, container, and installed-package identity;
- `BUILD_COMMANDS.txt` — literal configure/build commands;
- `PATCHES.json` — applied-patch inventory (currently empty); and
- `SHA256SUMS` — complete hash inventory for that output directory.

Firmware, preload, terminal, service-worker, browser harness, license bundle,
and final staging outputs are intentionally not claimed by this prototype
build.  Their exact set and hashes depend on #193's accepted media path and
must be added to the same manifest before the two-clean-build and browser boot
gates can pass.

Release validation is already fail-closed for that future staging directory.
Every output must carry a hash, size, and `asset_class`; the manifest must cover
the Wasm module, JavaScript/worker glue, firmware, terminal, service worker,
preload, browser harness, license bundle, build log, tool versions, patch
inventory, and browser evidence.  Controlled fixtures reject omitted firmware
or license material, substituted Wasm or JavaScript, and any staging inventory
that differs from the manifest.  This validates the contract only; it does not
select #193's media-specific files or assert that the browser boot gate passed.
