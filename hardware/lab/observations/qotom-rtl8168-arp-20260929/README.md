# RTL8168 ARP probe from a Lean device program — 2026-09-29

The LeanOS lab kernel (UEFI boot from the SSD image) ran `rtl8168-arp`
(`LeanOS/Net/Rtl8168.lean`) as a version-3 image under
`qotomRtl8168Policy`: the RTL8168E-VL at 01:00.0 (FreeBSD's `re0`) through
BAR2 (configuration offset 0x18), with receive and transmit rings in
executor scratch and the ring bases as address sinks.

```text
LEANOS-LAB/1 WIFI-BEGIN id=0x816810ec bar0=0xd0804004
WIFI 4001 0x2f900d00   TXCFG: hardware revision 8168E-VL
WIFI 4002 0xccc40e00   station address 00:0e:c4:cc:
WIFI 4003 0x000094a2                      a2:94
WIFI 4004 0x0000008b   media status: link up, full duplex, 100 Mb/s
WIFI 400c 0x70000000   transmit descriptor returned by the chip
WIFI 4007 0x5f011370   router address 70:13:01:5f:
WIFI 4008 0x00000f32                   32:0f
WIFI 4009 0x00000001   frames received
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

Independent checks from the wired workstation (192.168.6.62) on the same
switch:

* `tcpdump` captured the probe the program transmitted
  (`workstation-arp.txt`):
  `00:0e:c4:cc:a2:94 > ff:ff:ff:ff:ff:ff, ARP, Request who-has 192.168.6.1
  tell 0.0.0.0, length 60` — an RFC 5227 probe, so no address was claimed;
* the workstation's neighbour table has `192.168.6.1 lladdr
  70:13:01:5f:32:0f`, the router address the program read from the reply it
  received by DMA.

The program then stopped the MAC and cleared Bus Master; FreeBSD booted
normally and used `re0` afterwards.

ELF SHA256 `42852a6fec8323cf561cb8bcb57e4f29c8443afaf64c16e4ffa26757cec504d3` (no secrets). Capture SHA256 `7a7b8bd5a4112f0fb5b2d0cfb880360068e0aad41251c96ab67b87a60b00bbe7`.
