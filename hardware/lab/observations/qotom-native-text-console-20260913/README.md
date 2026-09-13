# Native Qotom text-console acceptance — 2026-09-13

This protected Win7 Legacy USB boot completes the physical acceptance check for
issue #335. The image was built from clean source and prepared revision
`9f5d8e5e8ce1514c355ff0965145b9f6229fe89b`. Its ELF SHA256 is
`747e1a96d123ec7e429a33cf8fa3f9daa1e9aedb0f653d7c21fe627ed78c41d8`.

During this exact boot, the operator watching the attached Qotom monitor
reported:

> yes i see the top boot line, then CPU then CONTROL then FINAL FAIL
> qotom-platform-pending. it's all visible on the monitor.

The observation establishes that LeanOS replaced the previously misleading
GRUB-only display and kept all four intended records visible through the
expected terminal rejection. No photo was required because the operator made
the report while the matching serial capture was active.

COM1 captured the same ordered kernel transcript at 38400 baud, 8N1, with no
flow control:

```text
LEANOS/24 BOOT target=qotom-j1900-candidate phase=cpu-diagnostic platform-admitted=0 cpl3=0
LEANOS/24 CPU profile=j1900-cpu-v1 codec=1 width=22 words=1,31,11,1970169159,1818588270,1231384169,198264,1050624,1104733119,3219913727,0,8834,0,0,2147483656,0,0,0,0,0,257,672139264 selection=65536
LEANOS/24 CONTROL profile=j1900-cpu-v1 codec=1 width=8 words=3328,0,0,0,0,0,0,0 readback=1
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The complete FTDI/null-modem capture has SHA256
`1c95bca648bc230d5854330ef87bb63aef2d10ea61f7b3db0771d76a5b72fbf2`.
The exact decoded diagnostic span has SHA256
`5fdb08efff06f1b01cf217ca5c35b6b01f9294c7f282aeca6fc9ab905f0fd94f`.
The generated replay accepted the recorded CPU and control values. After
34.321 seconds of post-terminal quiet, the external watchdog reset the board,
GRUB consumed the one-shot request, chained to FreeBSD, and authenticated SSH
returned. FreeBSD boot epoch advanced from `1789326999` to `1789332852`.

The actual legacy GRUB handoff is retained in
[`../qotom-native-blocking-ipc-20260913`](../qotom-native-blocking-ipc-20260913):
framebuffer kind 2, physical `0xb8000`, pitch 160, width 80, height 25, and 16
bits per character cell. Those values meet the generated early-console geometry
contract. The optional Multiboot2 console-header tag requests text support; it
does not require a display. The Qotom FADT `NO_VGA` flag is not used as blanket
VGA authority. This capability comes from GRUB's explicit EGA-text surface tag,
is bounded by the initial identity mapping, and is disabled before PCI
quarantine or page-root replacement.

The USB serial identity was `11758C40`. Post-recovery inspection verified the
active MBR FAT32 partition, clean filesystem, installed ELF and GRUB hashes, and
`request=none`. `capture.sh` and `install.sh` preserve the exact procedures.
