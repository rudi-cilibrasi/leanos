#!/usr/bin/env python3
"""Fail-closed classifier for the LeanOS qemu-wasm compatibility gate."""

import argparse
import json
import pathlib
import sys

ISO_BYTES = 14_749_696
MEDIA_MAPPING = "cdrom:/leanos.iso"


def fail(kind: str, detail: str) -> None:
    print(f"outcome=FAIL failure_class={kind} detail={detail}")
    raise SystemExit(1)


def protocol_lines(text: str) -> list[str]:
    return [line.rstrip("\r") for line in text.splitlines()
            if line.startswith("LEANOS/")]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("browser_result", type=pathlib.Path)
    parser.add_argument("native_serial", type=pathlib.Path)
    args = parser.parse_args()
    try:
        result = json.loads(args.browser_result.read_text(encoding="utf-8"))
        native = args.native_serial.read_text(encoding="utf-8")
    except (OSError, json.JSONDecodeError) as error:
        fail("browser-setup", str(error).replace(" ", "_"))

    probe = result.get("probe") or {}
    if probe.get("crossOriginIsolated") is not True:
        fail("browser-setup", "cross-origin-isolation-unavailable")
    if probe.get("mediaMapping") != MEDIA_MAPPING:
        fail("media-mapping", f"expected={MEDIA_MAPPING},actual={probe.get('mediaMapping')}")
    if probe.get("preloadSize") != ISO_BYTES:
        fail("preload", f"expected-bytes={ISO_BYTES},actual={probe.get('preloadSize')}")
    if result.get("title") == "abort" or probe.get("abort"):
        fail("runtime-abort", "qemu-wasm-aborted")
    if result.get("pageErrors"):
        fail("runtime-abort", "uncaught-page-error")
    actual = protocol_lines(result.get("transcript", ""))
    if result.get("waitError"):
        transcript = result.get("transcript", "")
        if not actual and ("Boot failed:" in transcript or
                           "No bootable device" in transcript):
            fail("firmware-media", "firmware-could-not-read-boot-media")
        fail("timeout", "browser-observation-bound-exceeded")

    title = result.get("title")
    if title != "exit=33" or probe.get("exitCode") != 33:
        if title and title.startswith("exit="):
            fail("guest-status", f"expected=33,actual={title[5:]}")
        fail("timeout", "missing-debug-exit")

    expected = protocol_lines(native)
    if not actual:
        transcript = result.get("transcript", "")
        if "Boot failed:" in transcript or "No bootable device" in transcript:
            fail("firmware-media", "firmware-could-not-read-boot-media")
        fail("protocol", "no-LeanOS-record")
    limit = max(len(expected), len(actual))
    for index in range(limit):
        left = expected[index] if index < len(expected) else "<missing>"
        right = actual[index] if index < len(actual) else "<missing>"
        if left != right:
            fail("protocol", f"first-divergent-record={index + 1}")
    print(f"outcome=PASS records={len(expected)} debug_exit=33")


if __name__ == "__main__":
    main()
