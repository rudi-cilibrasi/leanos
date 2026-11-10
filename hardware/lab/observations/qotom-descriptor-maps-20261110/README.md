# AHCI identify and RTL8168 ARP under descriptor maps — 2026-11-10

Issue #640 gave `qotomAhciPolicy` and `qotomRtl8168Policy` descriptor maps
(ADR 0021, decision 4). Each program's version-3 image declares its map, the
lab kernel's profile requires it, and the executor checks every scratch
store that touches a mapped field. Both programs ran once on the Qotom J1900
from branch `feat/qotom-descriptor-maps-640` (commit 283b0bda), booted
through the internal-disk GRUB's one-shot request (issue #620; no USB
stick). The completion lab image reset 30 s after `FINAL`, and FreeBSD came
back on its own each time.

The declared maps, decoded from the images' headers (kind, start, count,
stride):

| Program | Descriptor map |
| --- | --- |
| `ahci-identify` | (0, 0x8, 32, 32): the 32 command headers' CTBA; (0, 0x880, 120, 16): the PRD data bases before the IDENTIFY buffer |
| `rtl8168-arp` | (0, 0x8, 16, 16): the receive ring slots' buffer addresses; (0, 0x108, 240, 16): the transmit ring slots' |

## AHCI IDENTIFY DEVICE

`ahci-identify/serial.raw` (ELF SHA256 `38709d3167d15048821cf05dcc1228e4059d9496e78a02fffa574283c9dd5f2c`,
capture SHA256 `7ab1668a3f58ea69926827a0809cd125ebe4c44f5604a6de8c195f7406143453`):

```text
LEANOS-LAB/1 WIFI-BEGIN id=0x0f238086 bar0=0xd0916000
WIFI 3101 0xc720ff01   CAP
WIFI 3102 0x80000002   GHC
WIFI 3103 0x00000002   PI: port 1 only
WIFI 3106 0x00000123   PxSSTS: device present, Gen 2, active
WIFI 3105 0x00000006   PxCMD before: engines stopped
WIFI 3108 0x00000050   PxTFD after IDENTIFY: DRDY, no error
WIFI 3107 0x00000101   PxSIG: ATA device
WIFI 31ff 0x00000000   done
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

The register records are those of the 2026-09-29 run
(`../qotom-ahci-identify-20260929`). The IDENTIFY words decode to the same
drive that FreeBSD's `camcontrol identify ada0` reported after the run:

| Field | Lean program | FreeBSD |
| --- | --- | --- |
| Model (words 27–46) | `Hoodisk SSD` | `Hoodisk SSD` |
| Firmware (23–26) | `SBFM21.0` | `SBFM21.0` |
| Serial (10–19) | `H4MTCBC20133251` | `H4MTCBC20133251` |
| LBA48 sectors (100–103) | 250069680 | 250069680 |

So every store the program made into its command header and PRD passed the
descriptor check, and the controller followed them to the IDENTIFY data.

## RTL8168 ARP probe

`rtl8168-arp/serial.raw` (ELF SHA256 `592545c03e4996864a9b1d5ea0695338746713d8005b22db352b04b2982cdc07`,
capture SHA256 `cc2df20e2eda23ee860d8d2e7c3f1a96e4e8f9ef925b5cfc0060ec7031e006a5`):

```text
LEANOS-LAB/1 WIFI-BEGIN id=0x816810ec bar0=0xd0804004
WIFI 4001 0x2f900d00   TXCFG: hardware revision 8168E-VL
WIFI 4002 0xccc40e00   station address 00:0e:c4:cc:
WIFI 4003 0x000094a2                      a2:94
WIFI 4004 0x0000008b   media status: link up, full duplex
WIFI 400c 0x70000000   transmit descriptor returned by the chip
WIFI 4007 0x5f011370   router address 70:13:01:5f:
WIFI 4008 0x00000f32                   32:0f
WIFI 4009 0x00000001   frames received
WIFI 400a 0x00000001   broadcasts
WIFI 400b 0x00000000   errors
WIFI 40ff 0x00000000   done
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

with both 23-record register dumps (`41xx` before, `42xx` after) and no
`400d` or `400e`. These are the records `docs/net-rtl8168.md` ("Maintainer
hardware steps") expects. The after dump has `4237` = 0x00 (TE, RE and RST
clear), `423c` = 0x0000 and `4250` = 0x10 (the configuration registers
locked). It also shows the ring bases the program programmed:
TNPDS (`4220`) = 0x001b0100 and RDSAR (`42e4`) = 0x001b0000, the scratch
bus addresses of exactly the mapped transmit and receive rings (scratch at
0x1b0000).

The workstation (192.168.6.62, same switch) captured the probe the program
transmitted (`rtl8168-arp/workstation-arp.txt`, the first line):
`00:0e:c4:cc:a2:94 > ff:ff:ff:ff:ff:ff, ARP, Request who-has 192.168.6.1
tell 0.0.0.0`, an RFC 5227 probe. The later lines are FreeBSD's own ARP
traffic after it came back.

## FreeBSD's `re0` after the run (issue #577)

This was the first hardware run of the program with the #577 teardown. The
2026-09-29 program left FreeBSD's `re0` receiving exactly 256 frames, then
stalled until `ifconfig re0 down up`. After this run, without touching
`re0` (`rtl8168-arp/re0-before.txt`, `re0-after.txt`):

- FreeBSD booted and `re0` came up at 1000baseT full duplex;
- 400 pings from the workstation got 400 replies (0% loss);
- `re0` counted 646 input frames, well past 256, with no input errors.

So the teardown fix holds on the hardware: the receive stall of #577 no
longer occurs.
