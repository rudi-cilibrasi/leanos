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
* No TCP, and no IP traffic beyond ARP, ICMP echo and UDP echo on port 7.
* Calibration accuracy has no reference measurement, and an A/B from the
  development runner showed no measurable link-quality change.
* The driver runs in ring 0 of the lab kernel, outside the kernel's authority
  model (tracked in #454).

## Ring-3 network subject on the Qotom

Issue #450 moves ARP, ICMP echo and UDP echo out of the driver program into a
ring-3 network subject ([network-subject.md](network-subject.md)). With
`LEANOS_WIFI_NETWORK_SUBJECT` set, the `connect` program serves a frame
endpoint after DHCP (`LeanOS.Wifi.Endpoint.serve`):

* It yields each decapsulated data frame as Ethernet II.
* It transmits whatever reply the kernel leaves in its scratch.
* It answers nothing itself.

The driver keeps the PMK, the TK and the GTK, and it handles group-key
rotation. The DHCP client stays in the driver program for now; moving it to a
subject of its own is a follow-up. Without `LEANOS_WIFI_NETWORK_SUBJECT`,
`connect` with `LEANOS_WIFI_SERVE_SECONDS` still runs the ring-0 responder.
That is the baseline of the 2026-09-30 capture, kept until the ring-3 capture
replaces it.

`scripts/build-qotom-recovery-lab.py --network-subject` extends the
`--ipc-device-stream` flow of the audited `qotom-blocking-ipc-v1` profile.
After the fixed first exchange:

* Subject 2 (B) is the WiFi driver subject. It holds the device capability
  for the bound program.
* Subject 1 (A) runs the network subject. It is compiled from the same
  `subjects/net/main.c` and the same generated responder (`NetEcho.c`) as the
  q35 image, into A's text. Its frame buffer is the bottom of A's stack
  range.
* Frames cross through the audited bounded copy roots, which alias exactly
  A's two stack pages. A copy is sixteen bytes per `leanos_copy_root_transfer`,
  the primitive's audited bound. No root, alias or primitive changes.
* The dispatcher checks every copy against `leanos_frame_copy_check`, every
  device request against `leanos_device_authorize`, and every frame exchange
  against `leanos_blocking_ipc_event`.
* The blocking-IPC audit runs with its `--network-subject` contract.

The trust contract leaves the BCM43224 in D3hot with Command=0
([qotom-broadcom-d3.md](qotom-broadcom-d3.md)). Before binding, the lab
returns it to D0: its PMCSR advertises No_Soft_Reset, so the BARs survive. It
then requires Command to be still 0. This is a lab-only assignment step
outside the reviewed contract. A reviewed contract variant that admits the
Broadcom as assigned is still open.

None of this has run on the hardware yet. The q35 `network-subject` scenario
exercises the same subject, endpoint layout and witnesses.

### Maintainer steps for the capture

Run these on the development host in a checkout of the merged branch. The
board boots legacy BIOS, as for the 2026-10-07 keyboard stream. Use the flag
set recorded in
`hardware/lab/observations/qotom-device-stream-20261007/manifest.json`; the
`<flag set>` below stands for it.

1. Build the canonical inputs:

   ```sh
   ./scripts/build-image.sh
   ```

2. Run the keyless smoke test first. Generate the frame-source image for the
   Broadcom target and build the lab image:

   ```sh
   .lake/build/bin/leanos-wifi-gen net-bcm-frames build/net/net-bcm-frames.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/net/net-bcm-frames.bin --ipc-device-stream --network-subject
   ```

   The image touches no Broadcom register. It feeds the six q35 frames
   through the real Qotom path: copy roots, IPC, and the network subject in
   ring 3. Install and run it as in [Booting the image from the
   SSD](#booting-the-image-from-the-ssd):

   ```sh
   scp build/qotom-wifi-lab/leanos-qotom-lab.elf freebsd@192.168.6.21:/var/tmp/leanos-wifi.elf
   sha256sum build/qotom-wifi-lab/leanos-qotom-lab.elf
   ssh freebsd@192.168.6.21 sudo sh /var/tmp/install-ssd.sh <sha256>
   build/wifi/lab-trial.sh build/wifi/net450-smoke
   ```

   Expect the following in `build/wifi/net450-smoke/cycle-1/serial.raw`:
   * `SERVICE assign device=2:0.0 pmcsr=d3hot,d0`;
   * one `NET event=deliver`/`fetch` pair per frame, and a `send` for the
     three replies;
   * `WIFI 5101`/`5102` records from the frame source (each reply matched
     the reference);
   * `LEANOS/10 FINAL status=PASS network-subject=1 device-holder=2 frames=7
     fetches=7 replies=3 refusals=2`.

3. Run the WiFi capture. This image embeds the PMK: keep it under `build/`,
   never commit it, and never print the passphrase.

   ```sh
   LEANOS_WIFI_PSK="$(cat ~/.config/leanos/wifi-psk)" LEANOS_WIFI_DHCP=1 \
     LEANOS_WIFI_SERVE_SECONDS=90 LEANOS_WIFI_NETWORK_SUBJECT=1 \
     .lake/build/bin/leanos-wifi-gen connect build/wifi/net450.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/wifi/net450.bin --ipc-device-stream --network-subject
   ```

   Install it as in step 2 and start `build/wifi/lab-trial.sh
   build/wifi/net450`. Once `WIFI 0F11` (endpoint ready) shows the leased
   address, run these from a LAN host:

   ```sh
   ping -c 10 <leased address>
   printf 'ring 3 echo\n' | nc -u -w 2 <leased address> 7
   ```

   Optionally record the air side with `sudo tcpdump -i eno1 host <leased
   address>`. Expect:
   * ten echo replies;
   * the UDP payload echoed back;
   * one `NET event=fetch`/`send` pair per ARP, ICMP and UDP frame, and
     `WIFI 0F13` per transmitted reply;
   * a final `LEANOS/10 FINAL status=PASS network-subject=1 ...`.

   The retained serial stream contains decrypted payloads. Redact them before
   committing an observation, and never commit `net450.bin`.
