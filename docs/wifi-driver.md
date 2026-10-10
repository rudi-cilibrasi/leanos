# BCM43224 WiFi driver (lab)

LeanOS drives the Qotom's Broadcom BCM43224 (PCI `14e4:4353`, D11 core rev 23,
N-PHY rev 6, radio 2056 rev 11) with device programs written in Lean. The lab
kernel cannot run allocating Lean code, so the driver is expressed in a small
register-machine instruction set (`LeanOS/Wifi/Bytecode.lean`); a hosted
generator (`lake exe leanos-wifi-gen`) encodes a program and a runtime-free
executor performs only the effects each instruction names: MMIO,
configuration space, delays, scratch memory, FIFOs and serial records. The
executor's step is the generated C of `LeanOS/Wifi/Exec.lean`, proved equal
to `Sim.step` (ADR 0020); `hardware/wifi/wifi-gen-exec.h` supplies its hooks
and step loop, and `hardware/wifi/wifi-exec.h` the image parser.

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
(`/dev/mem`, `/dev/pci`), built together with the generated executor:
`lean --c=Exec.c LeanOS/Wifi/Exec.lean` (or `.lake/build/ir/LeanOS/Wifi/Exec.c`
after `lake build`), then
`cc -O2 -ffunction-sections -I<lean-prefix>/include -Ihardware/wifi
hardware/wifi/fbsd-runner.c Exec.c -Wl,--gc-sections`, where `<lean-prefix>`
is `lean --print-prefix` (only its headers are used). The same program image is spliced into the lab
kernel with `scripts/build-qotom-recovery-lab.py --wifi-program` and installed
by `hardware/wifi/install-lab.sh`. Hardware observations:
`hardware/lab/observations/qotom-wifi-scan-20260926`,
`qotom-wifi-connect-20260926`, `qotom-wifi-ping-20260926` and
`qotom-wifi-calibrated-20260927`.

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
and must never be committed.

What runs beyond association: brcmsmac's full N-PHY calibration (RSSI, TX
IQ/LO and RX IQ with the RC filter sweep; `calLevel := 3`, the Qotom default),
DHCP, and a responder that answers ARP and ICMP echo for the leased address
(`LeanOS/Wifi/Responder.lean`). Evidence:
`hardware/lab/observations/qotom-wifi-ping-20260926` and
`hardware/lab/observations/qotom-wifi-calibrated-20260927` (25/25 pings with
calibration on).

Known gaps:

* The PMU spur-avoid PLL update (`bcma_pmu_spuravoid_pllupdate`) is not
  ported; spur-avoid mode stays 0 on every channel (`SPURAVOID_DISABLE`,
  `PhyCfg.spurAvoidDisable`).
* The SNonce is hashed from timing jitter (TSF samples), a lab-grade source,
  not a vetted RNG.
* No group-key (GTK) rekeying: once the AP rotates its group key, broadcast
  frames (including ARP requests) stop decrypting. There is no IP traffic
  beyond ARP and ICMP echo (no UDP or TCP).
* Calibration accuracy has no reference measurement, and an A/B from the
  development runner showed no measurable link-quality change.
* The driver runs in ring 0 of the lab kernel, outside the kernel's authority
  model (tracked in #454).
