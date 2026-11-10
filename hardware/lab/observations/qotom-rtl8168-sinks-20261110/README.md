# RTL8168 ARP probe with every DMA root register in scratch — 2026-11-10

Issue #644: an address sink bounds only the values a program writes. A sink
register the program never writes keeps the previous owner's address, and a
program that makes the controller use it gets DMA there. The `rtl8168-arp`
program (`LeanOS/Net/Rtl8168.lean`) used to write only two of its four sinks,
TNPDS and RDSAR, and to set Bus Master at its first step. It now:

- turns Memory Space on and Bus Master off at its first step;
- also points THPDS at a zeroed high-priority ring slot in scratch, and DTCCR
  at a 64-byte tally area in scratch, with the Cmd bit clear. It never polls
  that queue or requests a dump;
- sets Bus Master only after all four sinks hold scratch addresses.

This observation is one run on the Qotom J1900 from branch
`docs/stale-sink-assumption`, booted through the internal-disk GRUB's one-shot
request. ELF SHA256 `a10953a2ee9f22b0afd4d5ff34aaa44a19ad2994238cafd2c9a46824fc753c1b`;
capture SHA256 `630f3989d925e8856e010e731ca9f7d0ded331e16925b788674160b71a91e734`.

## The root registers before and after

From the program's before (`41xx`) and after (`42xx`) dumps in `serial.raw`;
scratch starts at bus address 0x1b0000:

| Register | Before: as the previous owner left it | After the run |
| --- | --- | --- |
| DTCCR (0x10) | 0x00000000 | 0x001bb100: scratch + 0xB100, the tally area |
| TNPDS (0x20) | 0x00000000 | 0x001b0100: scratch + 0x100, the transmit ring |
| THPDS (0x28) | 0x00000000 | 0x001b0200: scratch + 0x200, the high-priority slot |
| RDSAR (0xE4) | 0x2d000000 (FreeBSD's receive ring) | 0x001b0000: scratch + 0x000, the receive ring |

All high dwords are 0. Before the change, DTCCR and THPDS stayed at 0, which
is physical address 0, through the whole run (`../qotom-descriptor-maps-20261110`).

## The run

`status=0` with the records of the earlier runs:

```text
LEANOS-LAB/1 WIFI-BEGIN id=0x816810ec bar0=0xd0804004
WIFI 4001 0x2f900d00   TXCFG: hardware revision 8168E-VL
WIFI 4004 0x0000008b   media status: link up
WIFI 400c 0x70000000   transmit descriptor returned by the chip
WIFI 4007 0x5f011370   router address 70:13:01:5f:
WIFI 4008 0x00000f32                   32:0f
WIFI 4009 0x00000001   frames received
WIFI 40ff 0x00000000   done
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

The run produced both 23-record dumps and no `400d` or `400e`. The after
dump has `4237` = 0, `423c` = 0 and `4250` = 0x10. The workstation captured
the RFC 5227 probe (`workstation-arp.txt`, first line).

Afterwards FreeBSD came back on its own, and its `re0` answered 400 of 400
pings and counted 644 input frames, without `ifconfig re0 down up`
(`re0-before.txt`, `re0-after.txt`).
