# AHCI IDENTIFY DEVICE from a Lean device program — 2026-09-29

The LeanOS lab kernel (UEFI boot from the SSD image) ran the `ahci-identify`
program (`LeanOS/Storage/Ahci.lean`) as a version-3 image under
`qotomAhciPolicy`: the SATA controller at 00:13.0 through its ABAR
(configuration offset 0x24, 2 KiB window), DMA into executor scratch, with
PxCLB and PxFB as address sinks.

```text
LEANOS-LAB/1 WIFI-BEGIN id=0x0f238086 bar0=0xd0916000
WIFI 3101 0xc720ff01   CAP
WIFI 3102 0x80000002   GHC: AHCI enabled, interrupts enabled
WIFI 3103 0x00000002   PI: port 1 only
WIFI 3106 0x00000123   PxSSTS: device present, Gen 2, active
WIFI 3105 0x00000006   PxCMD before: engines stopped
WIFI 3108 0x00000050   PxTFD after IDENTIFY: DRDY, no error
WIFI 3107 0x00000101   PxSIG: ATA device
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

Decoded IDENTIFY words (ATA strings store two characters per word, high byte
first), and FreeBSD's `camcontrol identify ada0` for the same disk after the
run:

| Field | Lean program | FreeBSD |
| --- | --- | --- |
| Model (words 27–46) | `Hoodisk SSD` | `Hoodisk SSD` |
| Firmware (23–26) | `SBFM21.0` | `SBFM21.0` |
| Serial (10–19) | `H4MTCBC20133251` | `H4MTCBC20133251` |
| LBA48 sectors (100–103) | 250069680 | 250069680 |

The program issued only IDENTIFY DEVICE, stopped the port's engines before
and after, and left Bus Master cleared; FreeBSD booted normally afterwards.

ELF SHA256 `395b43807686a5a2f5b9f7aa6ceef3df9b4f7dad1634cd3791dada27f7b5c94c` (no secrets). Capture SHA256 `65918e47bcd52499dad63d7a0793efe5bc54e79965e6317ca018e72e769a38b0`.
