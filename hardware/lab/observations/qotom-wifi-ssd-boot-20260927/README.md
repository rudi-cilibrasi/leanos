# LeanOS boots from the SSD, leases DHCP and answers ping — 2026-09-27

The lab stick's GRUB now uses `hardware/lab/grub-qotom-ssd.cfg.in`: it
located the FreeBSD disk by its boot partition UUID, read the image digest
from `/leanos/leanos-digest.cfg` on that disk's EFI system partition,
hash-checked `/leanos/leanos-qotom-lab.elf` (`leanos-qotom-lab.elf: OK`)
and booted it under the watchdog-protected one-shot request. The image was
installed from FreeBSD with `hardware/wifi/install-ssd.sh` in about 7 s,
without touching the stick.

LeanOS joined QUAIL, printed the lease and answered ping:

```text
LEANOS-LAB/1 WIFI-DHCP address=192.168.6.30
LEANOS-LAB/1 WIFI-DHCP router=192.168.6.1
LEANOS-LAB/1 WIFI-DHCP netmask=255.255.255.0
LEANOS-LAB/1 WIFI-DHCP lease-seconds=172800
LEANOS-LAB/1 WIFI-PING listening address=192.168.6.30
LEANOS-LAB/1 WIFI-PING echo-replies=25
```

From the wired workstation, `ping -c 25 192.168.6.30` received 25/25 with no
duplicates (the CCMP replay check drops retransmitted requests), RTT
6.5–15.5 ms, average 8.8 ms. The run ended `WIFI-END status=0` and FreeBSD
SSH returned (boot epoch `1790494590` to `1790496718`).

ELF SHA256 `c0341420bce9260c84ffb12587fb79e61fc78b7f3918c5ba961bc9647c18543b`
(embeds the network PMK; not retained). Capture SHA256 `a7f312d3ea6fcbc112e001ba738c3fef0572baaee275853b35b70902939bc37e` (COM1, 38400
8N1; no decrypted payload records).

Earlier the same night the mesh stopped answering our authentication
requests after many rapid failed joins; after about 50 minutes without
attempts it answered again. Join attempts are now spaced 2 s apart.
