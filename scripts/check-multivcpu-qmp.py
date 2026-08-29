#!/usr/bin/env python3
"""Validate and normalize the retained QMP inventory for issue #183."""

from __future__ import annotations

import json
import sys
from pathlib import Path


class InventoryError(ValueError):
    pass


def normalize(records: list[dict[str, object]]) -> list[dict[str, object]]:
    commands = [
        record.get("message", {}).get("execute")
        for record in records
        if record.get("direction") == "host-to-qemu"
    ]
    if commands != ["qmp_capabilities", "query-cpus-fast"]:
        raise InventoryError("unexpected QMP command sequence")
    replies = [
        record.get("message", {}).get("return")
        for record in records
        if record.get("direction") == "qemu-to-host"
        and isinstance(record.get("message", {}).get("return"), list)
    ]
    if len(replies) != 1 or len(replies[0]) != 2:
        raise InventoryError("QMP did not report exactly two processors")
    normalized = []
    for cpu in replies[0]:
        if not isinstance(cpu, dict) or not isinstance(cpu.get("props"), dict):
            raise InventoryError("malformed QMP processor record")
        props = cpu["props"]
        normalized.append({
            "cpu-index": cpu.get("cpu-index"),
            "qom-path": cpu.get("qom-path"),
            "socket-id": props.get("socket-id"),
            "core-id": props.get("core-id"),
            "thread-id": props.get("thread-id"),
        })
    normalized.sort(key=lambda cpu: cpu["cpu-index"])
    expected = [
        {"cpu-index": 0, "socket-id": 0, "core-id": 0, "thread-id": 0},
        {"cpu-index": 1, "socket-id": 0, "core-id": 1, "thread-id": 0},
    ]
    for actual, wanted in zip(normalized, expected, strict=True):
        for key, value in wanted.items():
            if actual[key] != value:
                raise InventoryError(f"QMP processor topology drifted at {key}")
        if not isinstance(actual["qom-path"], str) or not actual["qom-path"]:
            raise InventoryError("QMP processor lacks a stable qom-path")
    return normalized


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: check-multivcpu-qmp.py TRANSCRIPT OUTPUT")
    source, output = map(Path, sys.argv[1:])
    records = [json.loads(line) for line in source.read_text(encoding="utf-8").splitlines()]
    normalized = normalize(records)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        "# leanos-q35-multivcpu-inventory-v1\n"
        + "cpu-index\tsocket-id\tcore-id\tthread-id\tqom-path\n"
        + "".join(
            f"{cpu['cpu-index']}\t{cpu['socket-id']}\t{cpu['core-id']}\t"
            f"{cpu['thread-id']}\t{cpu['qom-path']}\n" for cpu in normalized
        ),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
