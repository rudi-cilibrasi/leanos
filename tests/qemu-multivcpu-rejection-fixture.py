#!/usr/bin/env python3
import json
import os
from pathlib import Path
import socket
import sys

if sys.argv[1:] == ["--version"]:
    print("QEMU multi-vCPU rejection fixture version 1")
    raise SystemExit(0)

serial = None
monitor = None
for index, argument in enumerate(sys.argv):
    if argument.startswith("file:"):
        serial = Path(argument.removeprefix("file:"))
    if argument == "-qmp":
        monitor = sys.argv[index + 1].removeprefix("unix:").split(",", 1)[0]
if serial is None or monitor is None:
    raise SystemExit(2)

Path(monitor).unlink(missing_ok=True)
with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as server:
    server.bind(monitor)
    server.listen(1)
    connection, _ = server.accept()
    with connection, connection.makefile("rwb", buffering=0) as stream:
        stream.write(json.dumps({"QMP": {"version": {}, "capabilities": []}}).encode() + b"\n")
        capabilities = json.loads(stream.readline())
        if capabilities != {"execute": "qmp_capabilities"}:
            raise SystemExit(2)
        stream.write(b'{"return":{}}\n')
        query = json.loads(stream.readline())
        if query != {"execute": "query-cpus-fast"}:
            raise SystemExit(2)
        cpus = [
            {"cpu-index": index, "qom-path": f"/machine/cpu[{index}]", "props": {
                "socket-id": 0, "core-id": index, "thread-id": 0
            }}
            for index in range(2)
        ]
        stream.write(json.dumps({"return": cpus}).encode() + b"\n")

terminal = "LEANOS/7 BOOTALLOC status=FAIL reason=topology-madt-generated-entries"
pre_cpl3 = [
    "LEANOS/15 DMA snapshot=1 topology=0001000800020002 bus=0 scanned=256 "
    "present=5 optional-absent=1 writes=5 readbacks=5 "
    "initial-bus-masters=1 initial-bus-master-mask=16 bus-master=disabled "
    "readback=exact generated-result=0 stage=pre-cpl3 result=PASS",
    "LEANOS/21 VTD-ACTIVATE order=validate,scrub,construct,publish,"
    "invalidate-context,invalidate-iotlb,enable,verify journal=2271560481 "
    "gsts=3221225472 fsts=0 rtaddr=1638400 generated-result=0 "
    "stage=pre-cpl3 result=PASS",
]
mode = os.environ.get("LEANOS_QEMU_FIXTURE_MODE", "success")
records = {
    "success": [*pre_cpl3, terminal],
    "missing": [],
    "authority-leak": [*pre_cpl3, terminal, "LEANOS/8 CPL3 status=PASS"],
}.get(mode)
if records is None:
    raise SystemExit(0 if mode == "reset" else 2)
serial.write_text("".join(record + "\n" for record in records), encoding="utf-8")
raise SystemExit(35)
