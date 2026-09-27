# LeanOS reports its DHCP lease and answers ping — 2026-09-26

The LeanOS lab kernel ran the Lean `connect` program with the responder
(`LeanOS/Wifi/Responder.lean`, 45 s window): it joined QUAIL, leased an
address and printed it as boot records, then answered ARP and ICMP echo:

```text
LEANOS-LAB/1 WIFI-DHCP address=192.168.6.30
LEANOS-LAB/1 WIFI-DHCP router=192.168.6.1
LEANOS-LAB/1 WIFI-DHCP netmask=255.255.255.0
LEANOS-LAB/1 WIFI-DHCP lease-seconds=172800
LEANOS-LAB/1 WIFI-PING listening address=192.168.6.30
LEANOS-LAB/1 WIFI-PING echo-replies=101
```

From the Linux workstation (192.168.6.62, wired): `ping -c 15 192.168.6.30`
received 15/15 (+8 duplicates), RTT 6.4–146.7 ms. The run ended
`WIFI-END status=0` and FreeBSD SSH returned (boot epoch `1790490625` to
`1790491891`). ELF SHA256
`a2583338495b3a3d442e2cabbd0c5a0023309ea45963b759ad51616aeebe13d1`; capture
SHA256 `fd86b03376494dca486faec5d7f91897c6446f241f518654981d8b4784bee054` (COM1, 38400 8N1; no decrypted payload records).

The duplicates were retransmissions of echo requests whose 802.11 ACK the
access point missed. The responder has since gained a CCMP replay check
(per-key packet numbers); from the FreeBSD development runner, 20/20 pings
were answered with no duplicates and 61 retransmitted frames dropped. That
change is not yet in the ELF above.

Transmission uses chain 1 only (`PhyCfg.txChainOverride := some 2`): with
both chains or chain 0 the access point frequently missed our ACKs.
