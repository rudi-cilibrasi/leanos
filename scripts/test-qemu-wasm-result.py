#!/usr/bin/env python3
"""Controlled negative fixtures for the qemu-wasm result classifier."""

import json
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
CHECK = ROOT / "scripts/check-qemu-wasm-result.py"
PROTOCOL = "LEANOS/10 BOOT target=x86_64-q35\nLEANOS/10 FINAL status=PASS\n"


def result(**changes):
    value = {
        "title": "exit=33",
        "status": "exit=33",
        "transcript": PROTOCOL,
        "probe": {
            "crossOriginIsolated": True,
            "mediaMapping": "cdrom:/leanos.iso",
            "preloadSize": 14_749_696,
            "exitCode": 33,
        },
        "console": [],
        "pageErrors": [],
        "waitError": None,
    }
    for key, replacement in changes.items():
        if key.startswith("probe_"):
            value["probe"][key[6:]] = replacement
        else:
            value[key] = replacement
    return value


def main():
    fixtures = {
        "success": (result(), None),
        "missing-isolation": (result(probe_crossOriginIsolated=False), "browser-setup"),
        "absent-preload": (result(probe_preloadSize=None), "preload"),
        "truncated-preload": (result(probe_preloadSize=1024), "preload"),
        "wrong-media": (result(probe_mediaMapping="ide:/leanos.iso"), "media-mapping"),
        "firmware-only": (result(
            transcript="SeaBIOS\nBoot failed: Could not read from CDROM\n",
            probe_exitCode=None, title="LeanOS gate", waitError="TimeoutError",
        ), "firmware-media"),
        "incomplete-protocol": (result(transcript=PROTOCOL.splitlines()[0]), "protocol"),
        "divergent-protocol": (
            result(transcript=PROTOCOL.replace("status=PASS", "status=FAIL")),
            "protocol",
        ),
        "extra-protocol": (result(transcript=PROTOCOL + "LEANOS/10 EXTRA status=PASS\n"), "protocol"),
        "guest-failure": (result(title="exit=35", probe_exitCode=35), "guest-status"),
        "runtime-abort": (result(title="abort", probe_abort="trap"), "runtime-abort"),
        "timeout": (result(title="LeanOS gate", probe_exitCode=None,
                           waitError="TimeoutError"), "timeout"),
    }
    with tempfile.TemporaryDirectory() as directory:
        tmp = pathlib.Path(directory)
        native = tmp / "native.serial"
        native.write_text(PROTOCOL, encoding="utf-8")
        for name, (fixture, expected_class) in fixtures.items():
            path = tmp / f"{name}.json"
            path.write_text(json.dumps(fixture), encoding="utf-8")
            completed = subprocess.run(
                [str(CHECK), str(path), str(native)],
                text=True, capture_output=True, check=False,
            )
            if expected_class is None:
                assert completed.returncode == 0, completed.stdout + completed.stderr
                assert "outcome=PASS" in completed.stdout
            else:
                assert completed.returncode != 0, name
                assert f"failure_class={expected_class}" in completed.stdout, (
                    name + ": " + completed.stdout + completed.stderr
                )
    print(f"qemu-wasm classifier fixtures passed ({len(fixtures)})")


if __name__ == "__main__":
    main()
