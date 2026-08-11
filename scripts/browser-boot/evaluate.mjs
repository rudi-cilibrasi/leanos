// Pure runtime-outcome decision for the LeanOS qemu-wasm browser harness.
//
// This function decides only the *runtime* outcome of a browser boot: did the
// pinned WebAssembly QEMU reach a guest debug-exit, or did it fail to isolate,
// abort, hang, or produce no serial output.  It deliberately does NOT judge the
// LeanOS protocol: the serial bytes are written back to the QEMU-shaped shim's
// `-serial file:` target and validated by the unchanged `scripts/run-image.sh`,
// exactly like a native run.  Keeping the two concerns separate is what lets a
// firmware-only or truncated transcript be rejected by the canonical protocol
// gate rather than by a browser-specific shortcut.
//
// Exit codes are chosen so the shim can return them to `run-image.sh`, whose
// classifier treats 33 as pass, 35 as guest-error, 124/137 as timeout, and any
// other value as a runtime/harness error.  A guest debug-exit is returned
// verbatim so both 33 (PASS) and 35 (guest FAIL) reach the runner unchanged.

export const OUTCOME = {
  NO_ISOLATION: { status: 'no-cross-origin-isolation', exitCode: 69 },
  RUNTIME_ABORT: { status: 'runtime-abort', exitCode: 70 },
  TIMEOUT: { status: 'timeout', exitCode: 124 },
  NO_SERIAL: { status: 'no-serial-output', exitCode: 71 },
  NO_GUEST_EXIT: { status: 'no-guest-exit', exitCode: 72 },
  GUEST_EXIT: { status: 'guest-exit', exitCode: null },
};

// captured: {
//   crossOriginIsolated: boolean,
//   title: string,            // 'exit=<n>' on debug-exit, 'abort' on runtime abort
//   serialBytes: number,      // bytes written to the MEMFS serial log
//   timedOut: boolean,        // observation bound exceeded without a terminal title
// }
export function evaluate(captured) {
  if (!captured.crossOriginIsolated) {
    return { ...OUTCOME.NO_ISOLATION, exitCode: OUTCOME.NO_ISOLATION.exitCode };
  }
  if (captured.title === 'abort') {
    return { ...OUTCOME.RUNTIME_ABORT };
  }
  if (captured.timedOut) {
    return { ...OUTCOME.TIMEOUT };
  }
  const match = /^exit=(\d+)$/.exec(captured.title || '');
  if (match) {
    const guestExit = Number(match[1]);
    if (!(captured.serialBytes > 0)) {
      // A debug-exit with no serial output is a media/preload failure, not a
      // guest result; never let it masquerade as a boot.
      return { ...OUTCOME.NO_SERIAL };
    }
    return { status: OUTCOME.GUEST_EXIT.status, exitCode: guestExit, guestExit };
  }
  return { ...OUTCOME.NO_GUEST_EXIT };
}
