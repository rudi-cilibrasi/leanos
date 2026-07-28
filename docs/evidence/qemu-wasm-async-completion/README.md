# qemu-wasm asynchronous completion checkpoint

This directory narrows issue
[#193](https://github.com/rudi-cilibrasi/leanos/issues/193) below the raw POSIX
worker function. It is failure evidence, not browser boot evidence.

## Result

The unchanged canonical ISO has SHA-256
`94b4c762823085159ec70ce5c728205934a35aed20bbd306342834f878e4d8c9`.
The instrumented runtime was built from qemu-wasm revision
`0ef7b4e2814b231705d8371dd7997f5b72e70baf` with Emscripten 3.1.50. Its
WebAssembly file has SHA-256
`ca59e9c60925a0e929fd11bdbf141d36b65c534e2997864ebe4265e4a22ee640`.
Chrome was 150.0.7871.128.

The browser was cross-origin isolated, preloaded all 14,749,696 ISO bytes, and
reached SeaBIOS READ(10) for LBA 17. The trace then proves this sequence:

1. `thread_pool_submit` queued the 2,048-byte read at offset 34,816.
2. An existing worker dequeued the request.
3. The raw POSIX worker function returned success (`ret=0`).
4. The worker scheduled `thread_pool_completion_bh`.
5. `aio_bh_enqueue` made the bottom half pending and called `aio_notify` while
   `notify_me=1`.
6. No `bh-consume`, `thread_pool_complete`, coroutine wake, or ATAPI DMA
   completion occurred before the 180-second bound.

This distinguishes the failure from worker non-execution. The completed worker
notification is lost or not consumed by the qemu-wasm AioContext event loop.
SeaBIOS consequently reports CD-ROM error `0003`.

The retained
[`browser-result.json`](browser-result.json) has SHA-256
`6d6e7c3bc08d8834c9f3024348003bb936018b72e8ad10c4c39e3e336d0d405b`.
Its decoded transcript has SHA-256
`cc4959ad701f565c04dd35e9b51e06bd99defdc96293ca1758ffa44d7884a504`.

## Reproduction

Apply [`thread-pool-trace.patch`](thread-pool-trace.patch) to the pinned
qemu-wasm source before the source build described in ADR 0011. Preserve the
existing trace arguments and add no guest or device changes:

```sh
git -C qemu-wasm checkout 0ef7b4e2814b231705d8371dd7997f5b72e70baf
git -C qemu-wasm apply \
  /path/to/leanos/docs/evidence/qemu-wasm-async-completion/thread-pool-trace.patch

emconfigure /src/configure --static --target-list=x86_64-softmmu \
  --cpu=wasm32 --cross-prefix= --without-default-features \
  --enable-system --with-coroutine=fiber --enable-virtfs \
  --extra-cflags="$EXTRA_CFLAGS" --extra-cxxflags="$EXTRA_CFLAGS" \
  --extra-ldflags="$EXTRA_LDFLAGS"
emmake make -j1 qemu-system-x86_64

LEANOS_QEMU_WASM_TIMEOUT_MS=180000 \
  node build/qemu-wasm-source-browser/probe.mjs \
  build/qemu-wasm-source-browser/thread-pool-result.json
```

Use the same Emscripten flags, preload construction, QEMU arguments, firmware,
browser harness, and isolated local server recorded by the compatibility gate.
The first browser launch may perform the service-worker reload; run the bounded
probe after that reload and retain any first-load error separately.

An experimental Emscripten-only synchronous call to `handle_aiocb_rw` removed
the thread-pool submission but did not change the final CD-ROM error within the
same bound. It is therefore not retained as a proposed fix.

## Remaining acceptance criterion

The gate still requires either an upstreamable qemu-wasm/Emscripten AioContext
wakeup fix or another pinned, unforked qemu-wasm revision that boots the exact
ISO bytes and produces every canonical LeanOS protocol record plus debug-exit
status 33. Native QEMU and the guest image remain unchanged.
