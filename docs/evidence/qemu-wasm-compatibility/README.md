# qemu-wasm compatibility gate checkpoint

This directory retains the first issue
[#193](https://github.com/rudi-cilibrasi/leanos/issues/193) compatibility-gate
run. It is failure evidence, not browser boot evidence.

The run used LeanOS revision
`5570136552d003522b7cdb0a0510432970df0763`, qemu-wasm-demo revision
`0208c86ea45253c26c0ea6907f6db2dec89eb7b2`, images revision
`b7c549b5e6f4c376f76483a03e983214421434ad`, and the prebuilt runtime with
SHA-256
`f53107a35029d676aa551cd00d042f4f65af39a89bf72464494321fafdf54191`.
Chrome was `150.0.7871.128`; Node.js was `24.18.0`.

The freshly built canonical ISO was 14,749,696 bytes with SHA-256
`94b4c762823085159ec70ce5c728205934a35aed20bbd306342834f878e4d8c9`.
The native QEMU 8.2.2 control passed all 346 exact protocol records and
debug-exit status 33. Its serial log had SHA-256
`d6558ae52babe8fed08d0a193d38c7346f0bb280a43748d6e62127699d1898e1`.

The browser result records `crossOriginIsolated=true`, the exact
`cdrom:/leanos.iso` mapping, and the complete 14,749,696-byte preload. The
runtime did not abort, but the 180-second observation ended at SeaBIOS with
CD-ROM error `0003`, no LeanOS record, and no debug exit. The repository
classifier reports:

```text
outcome=FAIL failure_class=firmware-media detail=firmware-could-not-read-boot-media
```

Run the maintained command from a clean checkout of the pinned demo:

```sh
LEANOS_QEMU_WASM_DEMO=/path/to/qemu-wasm-demo \
  ./scripts/run-qemu-wasm-compatibility.sh
```

The command verifies all runtime and tool pins, builds and runs the native
control, stages the same ISO bytes, and retains metadata, native output,
browser console/errors, server log, transcript, and verdict under
`build/qemu-wasm-compatibility/`.
