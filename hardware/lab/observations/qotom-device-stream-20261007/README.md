# Qotom keyboard stream over the audited blocking-IPC profile (2026-10-07)

Issue #449 stage 3: the Lean xHCI keyboard program runs on the Qotom J1900
for ring-3 subject 1 under the audited `qotom-blocking-ipc-v1` profile. Each
key a person types crosses the verified blocking IPC to ring-3 subject 2,
which echoes it.

## Build

```sh
LEANOS_KBD_SECONDS=60 LEANOS_KBD_IDLE=25 LEANOS_KBD_TRACE=1 \
  .lake/build/bin/leanos-wifi-gen kbd-service kbd-service-trace.bin
python3 scripts/build-qotom-recovery-lab.py --prepared-repo . \
  <the qotom-platform-admission-20260913 flag set> \
  --lab-program kbd-service-trace.bin --ipc-device-stream
```

* The flag set is the one recorded in `manifest.json`: the full PCI trust
  chain, `--bsp-topology`, the entry, exception and blocking-IPC integration
  stages, plus `--ipc-device-stream`.
* The program image is `kbd-service-trace.bin`, SHA256
  `b9297678cad21f62fa0c07ec3be650db7b2688057d78c9cd578836ee34e7ccf2`. It is
  the yield-per-key form with a 100 ms HID idle rate and a raw-report trace
  (`WIFI 2104`). It contains no secrets.
* The ELF is `leanos.sha256`. The build also passed the blocking-IPC audit
  with the `--device-stream` contract (`blocking-ipc-integration-audit.json`).
  That contract fixes subject A's syscall trace as `4,4,8,60,8,61` and
  subject B's as `10,11,12,7,9,7,9`. It also requires four generated-witness
  checks, one device-invocation site and one bind site.

## Run

The board booted in legacy BIOS mode, because the whole-platform profile
admits only that firmware handoff. The run went through the USB watchdog
recovery flow (`build/wifi/lab-trial.sh`). The USB keyboard was a Chicony
04f2:0402 attached directly to a root port; the driver now also probes root
ports after the hub path. A person typed `hello lean⏎` repeatedly during the
60-second window.

## Result (`cycle-1/serial.raw`)

```text
LEANOS-LAB/1 PLATFORM-ADMISSION profile=qotom-j1900-clbtm210-v2 version=2 status=PASS cpl3-authority=1 ...
LEANOS-LAB/1 SERVICE grant subject=1 device=0:20.0 bind=accepted policy=admitted
LEANOS-LAB/1 QOTOM-IPC-READY profile=qotom-blocking-ipc-v1 subjects=2 ...
LEANOS-LAB/1 KBD ready vendor=0x04f2 product=0x0402 type-now
LEANOS/10 IPC event=deliver receiver=2 sender=1 exact=1 echo=h
...
LEANOS-LAB/1 KBD reports=648
LEANOS-LAB/1 KBD session-end keys=231
LEANOS-LAB/1 SERVICE end subject=1 status=0 code=0x00000000
LEANOS/10 FINAL status=PASS events=231 blocks=233 deliveries=232
```

The 231 echoed keys are exactly `hello lean⏎` typed 21 times. Every
exchange's four edges were checked against `leanos_blocking_ipc_event`. The
complete serial stream has SHA256
`f78798ab7d036a5f78a673994d90d57dfb4027f31e952a9ab3020c79579ce88b`. After the
terminal halt the watchdog reset the board and chained back to FreeBSD
(`cycle-1/reboot.txt`).

## Scope

* This is lab evidence for one named ELF on one board.
* The executor runs in ring 0 on subject 1's behalf (ADR 0022 option (a)).
* The xHCI's DMA is confined only by the program's address-sink policy: the
  J1900 has no IOMMU (ADR 0021).
* The runner's lab classifier rejects device-program records, so the cycle
  has no `result.json`. The transcript above is the evidence.
