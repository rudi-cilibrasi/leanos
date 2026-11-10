# Device programs under the Bus Master gate — 2026-11-10

Issue #644: the executor now refuses to set a device's Bus Master until the
program has written both dwords of every address sink of its policy, and the
lab kernel clears Bus Master before a program starts. Every DMA program was
reordered to write its sinks first. These runs on the Qotom J1900, from
branch `feat/busmaster-gate-644` (commit 62fe8e6a), check that the reordered
programs still work on the hardware. Each was booted through the
internal-disk GRUB's one-shot request (issue #620; no USB stick), and FreeBSD
came back on its own after each.

## AHCI IDENTIFY DEVICE (`ahci-identify/`)

Bus Master now follows the PxCLB and PxFB writes. `status=0`, with the
register records of the earlier runs (`../qotom-descriptor-maps-20261110`):
CAP `c720ff01`, PI port 1, PxSSTS `0x123`, PxTFD after IDENTIFY `0x50` (DRDY,
no error). The IDENTIFY data decodes to the same drive as FreeBSD's
`camcontrol identify ada0`: model `Hoodisk SSD`, firmware `SBFM21.0`, serial
`H4MTCBC20133251`, 250,069,680 LBA48 sectors.

ELF SHA256 `20b15266f6c50d6b755990644a64cf5d5e32e6db1a9c3ab95e3a9abc6cf09358`;
capture SHA256 `c7adad8aa6c31e7e72dff8b89ac4dd1b3a3543b2515799020f13265f526cfcc4`.

## RTL8168 ARP probe (`rtl8168-arp/`)

`status=0` with the same records: transmit status `0x70000000`, router
70:13:01:5f:32:0f, one frame received, both register dumps and no teardown
fault. The after dump shows the four sinks in scratch: DTCCR `0x001bb100`,
TNPDS `0x001b0100`, THPDS `0x001b0200`, RDSAR `0x001b0000`. Afterwards
FreeBSD's `re0` answered 400 of 400 pings and counted 625 input frames,
without `ifconfig re0 down up` (`re0-before.txt`, `re0-after.txt`).

ELF SHA256 `187c1bce691303059ddc60eae4c6011052360362c00339c8a21190133c39db00`;
capture SHA256 `95dcde765fc63e7f9e4311c8fb9ca39199680c6568a5e97f04d0d5039c85a5ec`.

## xHCI keyboard, unattended (`kbd/`)

The Bay Trail xHCI setup now sets Bus Master after DCBAAP, CRCR, ERDP and
ERSTBA. It writes ERSTBA while ERSTSZ is still 0 and starts the event ring
after Bus Master, by writing ERSTSZ and ERSTBA's high dword again. The
program ran a 15-second session with nobody at the keyboard:

```text
LEANOS-LAB/1 KBD ready vendor=0x04f2 product=0x0402 type-now
LEANOS-LAB/1 KBD reports=0
LEANOS-LAB/1 KBD session-end keys=0
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

So the controller came up and its command and event rings worked: the
program addressed the attached keyboard and read its descriptors
(vendor `04f2`, product `0402`) before reporting it ready. Key reports were
not exercised, since nobody typed.

ELF SHA256 `392d7b4552c896dcb9e500fc5d18055fb54830ebcc1c2e51770a0131db502b32`;
capture SHA256 `bbbb7b0858f124192262138ef37ef0cd7e66f47d745538541d740097b65d0d57`.
