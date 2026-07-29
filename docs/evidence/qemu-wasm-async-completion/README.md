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
`30db2e429f641a6f90b4f901bf9c716474806469017c47de4dc95b20c2625a05`.
Chrome was 150.0.7871.128.

The browser was cross-origin isolated, preloaded all 14,749,696 ISO bytes, and
reached SeaBIOS READ(10) for LBA 17. The trace then proves this sequence:

1. `thread_pool_submit` queued the 2,048-byte read at offset 34,816.
2. An existing worker dequeued the request.
3. The raw POSIX worker function returned success (`ret=0`).
4. The worker scheduled `thread_pool_completion_bh`.
5. `aio_bh_enqueue` made the bottom half pending and called `aio_notify` while
   `notify_me=1`.
6. A marker armed at that enqueue point observed no later
   `aio_ctx_prepare`, `aio_ctx_check`, or `aio_ctx_dispatch` call for the same
   context during the 180-second bound.
7. No `bh-consume`, `thread_pool_complete`, coroutine wake, or ATAPI DMA
   completion occurred.

This distinguishes the failure from worker non-execution. The completed worker
notification does not cause the GLib event loop to re-enter the marked
AioContext; the loss occurs before its check/dispatch consumption path. SeaBIOS
consequently reports CD-ROM error `0003`.

The retained
[`browser-result.json`](browser-result.json) has SHA-256
`6d6e7c3bc08d8834c9f3024348003bb936018b72e8ad10c4c39e3e336d0d405b`.
Its decoded transcript has SHA-256
`cc4959ad701f565c04dd35e9b51e06bd99defdc96293ca1758ffa44d7884a504`.
The more narrowly instrumented
[`aio-context-result.json`](aio-context-result.json) has SHA-256
`c4e745f49485803da2e343fa100fe66eba35e268f5def815688101d27f444867`;
its decoded transcript has SHA-256
`b35fcb5eb13d7c32b91acd7bfaf151cb855cf15f8331417fbb537b1c4d4daf80`.

## Source-level blocker

The pinned build has `CONFIG_EVENTFD` undefined. Consequently QEMU
`event_notifier_init` uses `g_unix_open_pipe`, and `aio_notify` depends on
pipe readiness to interrupt GLib's wait.

That contract is unavailable in the pinned Emscripten runtime. In the exact
build image (digest
`sha256:c9ce53b140c7e9c2e5bbbfacb5c27680fc5b49d94c896b56cbefd29898eb8b32`),
Emscripten 3.1.50's `library_syscall.js` implements `__syscall_poll` as one
readiness scan and never reads its `timeout` argument. Its
`__syscall__newselect` explicitly says that timeouts on `PIPEFS` are ignored
and treated as zero. There is therefore no blocking browser primitive behind
QEMU's pipe EventNotifier that another pthread can interrupt.

Four Emscripten-only experiments were rejected:

1. Capping QEMU's host-loop timeout at 1 ms compiled successfully but produced
   the exact original `browser-result.json` SHA-256
   `6d6e7c3bc08d8834c9f3024348003bb936018b72e8ad10c4c39e3e336d0d405b`.
2. Replacing the Emscripten wait with `emscripten_sleep(1)` plus a nonblocking
   readiness scan produced the same exact result hash.
3. Having the worker additionally enqueue a no-op on Emscripten's system proxy
   queue for `emscripten_main_runtime_thread_id()` also failed to re-enter
   `aio_ctx_prepare`, `aio_ctx_check`, or `aio_ctx_dispatch`.
4. Recording the AioContext's creating pthread and proxying
   `aio_poll(ctx, false)` directly to that thread from `aio_notify` also
   failed. The 41,503,914-byte WebAssembly build had SHA-256
   `afa65863198a2e5ddaf6e2aea57ef2a67f000b58936cf1c8f3045ba33042d6c2`.
   During the 120-second bound, the raw worker again returned success and
   enqueued its completion BH, but the proxied call did not consume the BH or
   produce any AioContext check/dispatch trace.

The retained
[`proxy-wakeup-result.json`](proxy-wakeup-result.json) has SHA-256
`dd4ee2049f5613e8d85d2a500f7a0b9a59b7f350912901c57788e60d2946f942`.
It preloaded the unchanged 14,749,696-byte ISO and records the third
experiment's 180-second bound. The fourth experiment is retained as
[`home-thread-aio-poll.patch`](home-thread-aio-poll.patch) and
[`home-thread-aio-poll-result.json`](home-thread-aio-poll-result.json); the
result has SHA-256
`284095939fa8bc5526bbaa180079a36d31111bf8ba59b605f001d79d18fa8441`.
These results rule out a timeout cap, an Asyncify timer yield, a generic
Emscripten proxy notification, and proxying one nonblocking AioContext poll to
its owner as upstreamable fixes. The target pthread is itself inside QEMU's
non-yielding host loop, so work queued to its Emscripten proxy queue cannot
provide the missing wakeup. Closing the wakeup requires an Emscripten-aware
QEMU main-loop integration that yields control while preserving event-loop
ownership, or a pinned unforked runtime where QEMU's EventNotifier has
supported cross-thread wake semantics.

### Single-thread TCG control

The supported QEMU argument `-accel tcg,thread=single,tb-size=500` changes the
failure boundary without changing the ISO, q35 devices, one-vCPU scope, or
network policy. In a 60-second diagnostic run, the same worker completed and
the owner loop consumed `thread_pool_completion_bh`. The runtime then aborted
before firmware because qemu-wasm's dynamic TCG module called
`instantiate_wasm` on a thread whose JavaScript module had no initialized
`__wasm32_tb.tb_ptr_ptr`.

The retained
[`single-thread-tcg-result.json`](single-thread-tcg-result.json) has SHA-256
`b719de2328c4f36c66ab6d3f8b32376c6da7752ebe36405dbb0f84ce000c4094`.
It used the pinned source revision and Emscripten version above, the unchanged
ISO, Chrome 150.0.7871.128, and the diagnostic runtime with SHA-256
`46b189292f66d8f0d060d8f6f4e9237fc7ef577af64fbe46a72efe76bceda08a`.
That runtime includes the trace instrumentation and rejected owner-thread
experiment, so this is not acceptance evidence or a proposed configuration.
It does establish a distinct runtime-abort boundary and prevents presenting
single-thread TCG as an invocation-only media fix.

Reproduce it by changing only the compatibility gate's accelerator argument
to:

```text
-accel tcg,thread=single,tb-size=500
```

Then run the source-browser probe above with
`LEANOS_QEMU_WASM_TIMEOUT_MS=60000`. The maintained gate remains on the
original pinned accelerator configuration.

## Reproduction

Apply [`thread-pool-trace.patch`](thread-pool-trace.patch) to the pinned
qemu-wasm source before the source build described in ADR 0011. Preserve the
existing trace arguments and add no guest or device changes:

```sh
git -C qemu-wasm checkout 0ef7b4e2814b231705d8371dd7997f5b72e70baf
git -C qemu-wasm apply --unidiff-zero --whitespace=nowarn \
  /path/to/leanos/docs/evidence/qemu-wasm-async-completion/thread-pool-trace.patch
# For the rejected owner-thread dispatch experiment only:
git -C qemu-wasm apply --whitespace=nowarn \
  /path/to/leanos/docs/evidence/qemu-wasm-async-completion/home-thread-aio-poll.patch

emconfigure /src/configure --static --target-list=x86_64-softmmu \
  --cpu=wasm32 --cross-prefix= --without-default-features \
  --enable-system --with-coroutine=fiber --enable-virtfs \
  --extra-cflags="$EXTRA_CFLAGS" --extra-cxxflags="$EXTRA_CFLAGS" \
  --extra-ldflags="$EXTRA_LDFLAGS"
emmake make -j1 qemu-system-x86_64

LEANOS_QEMU_WASM_TIMEOUT_MS=180000 \
  node build/qemu-wasm-source-browser/probe.mjs \
  build/qemu-wasm-source-browser/aio-context-result.json
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
