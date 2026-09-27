# BCM43224 WiFi driver (lab)

LeanOS drives the Qotom's Broadcom BCM43224 (PCI `14e4:4353`, D11 core rev 23,
N-PHY rev 6, radio 2056 rev 11) with device programs written in Lean. The lab
kernel cannot run allocating Lean code, so the driver is expressed in a small
register-machine instruction set (`LeanOS/Wifi/Bytecode.lean`); a hosted
generator (`lake exe leanos-wifi-gen`) encodes a program and a runtime-free C
executor (`hardware/wifi/wifi-exec.h`) performs only the effects each
instruction names: MMIO, configuration space, delays, scratch memory, FIFOs
and serial records.

| Layer | Modules |
| --- | --- |
| Machine, simulator | `Bytecode`, `Sim` |
| Chip bring-up, microcode | `Bcm43224` |
| N-PHY and radio (brcmsmac port, ISC) | `NPhy`, `NPhyTables`, `NPhyTablesData`, `NPhyWorkarounds`, `Radio2056`, `NPhyInit` |
| MAC receive/transmit, TX descriptors, power | `Mac`, `Tx` |
| Station management, handshake, DHCP | `Mlme`, `Handshake`, `DevCrypto`, `DevCcmp`, `DevDhcp`, `Connect` |
| Reference protocol library (hosted) | `Bytes`, `Sha1`, `Pbkdf2`, `Aes`, `Eapol`, `Ieee80211`, `Dhcp` |

Frames move by programmed I/O (RX direct-FIFO mode, PIO TX), so no DMA engine
is started. Device crypto is checked against the reference library in the
simulator (`leanos-wifi-devcrypto`, `leanos-wifi-devccmp`,
`leanos-wifi-hssim`, `leanos-wifi-dhcpsim`) and the simulator against the C
executor (`leanos-wifi-xcheck`); the reference library passes published
vectors (`leanos-wifi-vectors`).

Development runs from FreeBSD userland with `hardware/wifi/fbsd-runner.c`
(`/dev/mem`, `/dev/pci`); the same program image is spliced into the lab
kernel with `scripts/build-qotom-recovery-lab.py --wifi-program` and installed
by `hardware/wifi/install-lab.sh`. Hardware observations:
`hardware/lab/observations/qotom-wifi-scan-20260926` and
`qotom-wifi-connect-20260926`.

## Booting the image from the SSD

The lab stick can instead load the LeanOS image from the FreeBSD disk's EFI
system partition, so updates no longer touch the stick. Install the generic
`hardware/lab/grub-qotom-ssd.cfg.in` (rendered with the FreeBSD boot partition
UUID) as the stick's `boot/grub/grub.cfg` once. GRUB locates the FreeBSD disk
by that UUID and reads `/leanos/leanos-digest.cfg`, `/leanos/leanos.sha256`
and `/leanos/leanos-qotom-lab.elf` from its `gpt1`. It boots LeanOS only when
the one-shot request names that digest and the ELF hash matches; otherwise it
falls back to FreeBSD as before. The stick keeps GRUB, the one-shot request
and the watchdog scripts.

Update an image from FreeBSD with `hardware/wifi/install-ssd.sh <sha256>`
(it expects the ELF at `/var/tmp/leanos-wifi.elf` and keeps the previous
image in `/leanos/previous/`), then run
`scripts/run-qotom-recovery-lab.py --image-on-ssd ...`.

Program images for `connect` embed the network PMK (from `LEANOS_WIFI_PSK`)
and must never be committed. Known gaps: calibrations are not ported, the
PMU spur-avoid PLL update is replaced by `SPURAVOID_DISABLE`, the SNonce comes
from timer jitter, and nothing beyond DHCP (ARP, IP traffic, rekeying) runs.
