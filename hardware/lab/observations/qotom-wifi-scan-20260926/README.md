# Qotom WiFi scan under LeanOS — 2026-09-26

The LeanOS lab kernel ran a Lean-authored BCM43224 WiFi driver program and
received 802.11 beacons from the local network on channel 6. This is the
first reception by LeanOS itself; the same program had earlier been
developed against the card from FreeBSD userland through
`hardware/wifi/fbsd-runner.c`.

The driver is `LeanOS/Wifi/*`: device programs written in a small Lean
instruction-set DSL (`LeanOS/Wifi/Bytecode.lean`) and executed by the
runtime-free C executor `hardware/wifi/wifi-exec.h`, spliced into the lab
kernel by `scripts/build-qotom-recovery-lab.py --wifi-program`. PHY, radio
and MAC sequences are ported from Linux brcmsmac (ISC). Reception uses the
receive FIFO's programmed-I/O registers; no DMA engine is started.

Program `scan6` (`lake exe leanos-wifi-gen scan6 build/wifi/scan6.bin
build/wifi/fw`, firmware split from `/lib/firmware/brcm/bcm43xx-0.fw`):
SHA256 `d7ace8bf86a7134783b8d65b489682a780ce78e721bc12da48f59fc12d5658f7`.
ELF SHA256 `9d5e48f8521fe58b84dda4cc36e255380f78e7579ce216588a52d463c032d920`.
Raw capture SHA256
`00e36e99e4d8da0cabaa1835a613cd3454c022faa456bf566f8ff5adb348080d`.

The program identified the card, reset the D11 core, booted microcode
610.812, applied init values, initialised the N-PHY (tables, workarounds,
radio 2056 rev 11 power-up, channel 6 with spur avoidance disabled, init
body without calibrations), enabled the MAC promiscuously and parsed 40
received frames (39 beacons). BSSIDs advertising `QUAIL`:
`c4:f1:74:13:8a:47`, `78:76:89:c3:a5:f4`, `e8:d3:eb:d8:02:26`,
`c4:f1:74:03:66:a7`, `e8:d3:eb:c8:49:86`.

The run ended `WIFI-END status=0`, then the unchanged terminal
`FINAL status=FAIL reason=qotom-platform-pending`; the watchdog-protected
one-shot request was consumed and FreeBSD SSH returned (boot epoch
`1790488767` to `1790488880`; `cycle-1/recovery.json`). Serial: FTDI/null-modem COM1,
38400 baud, 8N1, no flow control. The runner's classifier does not know the
WiFi records and rejects the transcript; the capture itself is retained here.

Not established: transmission, association, calibration quality, receive
sensitivity, or any property of the lab kernel beyond this run.
