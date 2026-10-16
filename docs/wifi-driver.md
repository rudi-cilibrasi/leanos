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
rotation ([Group-key rotation](#group-key-rotation-issue-557)). Since
issue #556 the driver in this mode runs no DHCP client: it serves the
link-only endpoint (`LeanOS.Wifi.Endpoint.serveLink`) and the
ring-3 DHCP subject leases the address ([DHCP subject on the
Qotom](#dhcp-subject-on-the-qotom)). `LEANOS_WIFI_DRIVER_DHCP=1` keeps the
issue #450 compatibility path, in which the driver leases the address and
hands it to the network subject in the configuration record; the
`--network-subject` lab image without `--dhcp-subject` needs it. Without
`LEANOS_WIFI_NETWORK_SUBJECT`, `connect` with `LEANOS_WIFI_SERVE_SECONDS`
still runs the ring-0 responder, the baseline of the 2026-09-30 capture.

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
applies the reviewed assignment variant
`qotom-j1900-pci-trust-v1-bcm43224-assign-v1`
([qotom-broadcom-assignment.md](qotom-broadcom-assignment.md)). One PMCSR
store returns the device to D0. After the recovery delay the header, BARs,
PCIe status and Transactions Pending must match, and the program policy must
be assignable (no DMA, never Bus Master). Two generated checks decide; any
mismatch stops at `qotom-broadcom-assign`. The builder therefore requires
`--broadcom-d3` and `--pci-trust-contract` with `--network-subject`.

The 2026-10-12 capture ran this path on the Qotom (issue #450). The q35
`network-subject` scenario exercises the same subject, endpoint layout and
witnesses.

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

   The program touches no Broadcom register; the only Broadcom store is the
   assignment variant's PMCSR write. The program feeds the six q35 frames
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
   * `BROADCOM-ASSIGN profile=qotom-j1900-pci-trust-v1-bcm43224-assign-v1
     device=2:0.0 status=0 contract=1 pmcsr-before=16395 command-before=0
     d0-attempted=1 pmcsr-after=16392 command-after=0 bar0=3497000964 bar1=0
     polls=2 device-status=25 admitted=1` (`polls` may be higher), then
     `SERVICE grant subject=1 ... bind=accepted`. This record is the
     hardware validation of the assignment variant (issue #559). A nonzero
     `status` ends at `FINAL status=FAIL reason=qotom-broadcom-assign`; keep
     that serial stream, since its fields show which check refused (status
     table in [qotom-broadcom-assignment.md](qotom-broadcom-assignment.md));
   * one `NET event=deliver`/`fetch` pair per frame, and a `send` for the
     three replies;
   * `WIFI 5101`/`5102` records from the frame source (each reply matched
     the reference);
   * `LEANOS/10 FINAL status=PASS network-subject=1 device-holder=2 frames=7
     fetches=7 replies=3 refusals=2`.

3. Run the WiFi capture. This image embeds the PMK: keep it under `build/`,
   never commit it, and never print the passphrase.

   The serve window must stay at most 45 seconds: the lab watchdog is armed
   for 120 ticks and the join takes about 55 seconds.

   ```sh
   LEANOS_WIFI_PSK="$(cat ~/.config/leanos/wifi-psk)" LEANOS_WIFI_DRIVER_DHCP=1 \
     LEANOS_WIFI_SERVE_SECONDS=45 LEANOS_WIFI_NETWORK_SUBJECT=1 \
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

## DHCP subject on the Qotom

Issue #556 moves the DHCP client out of the driver
([network-subject.md](network-subject.md#dhcp-as-its-own-subject)). With
`LEANOS_WIFI_NETWORK_SUBJECT` and without `LEANOS_WIFI_DRIVER_DHCP`, the
`connect` program joins, runs the 4-way handshake, and then serves the
link-only endpoint (`LeanOS.Wifi.Endpoint.connectAndServeLink`):

* Its first record is the 6-byte link record, our hardware address. It
  chooses no IPv4 address, and `WIFI 0F17` marks the endpoint up.
* It yields every decapsulated data frame as Ethernet II, and a 1-byte tick
  after each second of TSF time.
* It transmits whatever frame the kernel leaves in its scratch.

The driver keeps the PMK, the TK, the GTK and the frame transport, and
nothing else.

`scripts/build-qotom-recovery-lab.py --dhcp-subject` extends
`--network-subject`. The audited `qotom-blocking-ipc-v1` profile has two
subjects, and the bounded copy roots alias only A's stack pages. So the
DHCP subject and the echo subject take turns in subject A:

* Subject 2 (B) is the WiFi driver subject, as before.
* Subject 1 (A) first runs the DHCP subject: `subjects/dhcp/main.c` with the
  generated client (`NetDhcp.c`), the same sources as the q35 subject B. Its
  frame buffer and registers are the bottom of A's stack range.
* When the DHCP subject sends its lease on endpoint 13, the kernel holds it.
  It zeroes both of A's stack pages through the writable copy-out root, then
  restarts A fresh at `qotom_echo_subject_entry`. That is the echo subject:
  `subjects/echo/main.c` with `NetEcho.c`, the same sources as the q35
  subject C. The echo subject receives the lease on endpoint 13 and answers
  only for it.
* Every copy is checked against `leanos_frame_port_check`, with A's current
  occupant as the caller, the window's owner and the served port. Every
  device request is checked against `leanos_device_authorize`. Every frame
  exchange is checked against `leanos_blocking_ipc_event`. The lease
  exchange is not, because the kernel holds it across the restart.
* The blocking-IPC audit runs with its `--dhcp-subject` contract. It counts
  one more copy-out site than `--network-subject`: the scrub.
* A's text now holds the asm subjects, the DHCP client and the echo
  responder, about 5.5 KiB, so it spans **two pages**. The copy roots
  therefore protect six frames, not five. The image uses the DHCP-subject
  inventory variant of `LeanOS.QotomCopyRootPublication` (variant 1:
  `protected=6 removed-aliases=4 retained-present=4087 aliases=2`), and the
  `COPY-ROOTS` record must show exactly those counts. The ordinary variant
  (`protected=5 removed-aliases=3 retained-present=4088`) is rejected for
  this image, and the reverse holds for every other image. The kernel also
  requires A's text to span exactly two pages here and one page otherwise,
  and the lab build refuses an ELF whose inventory differs from its variant.
  `boot/boot.S` marks every page of A's text user read-only executable, as
  the generated boot plan classifies it; it used to mark only the first,
  which would have left the DHCP and echo code on a supervisor page. The
  Qotom path never reaches the q35 boot-plan comparison, so the copy-root
  step checks those leaves itself (`qotom-root-user-text`). See [ADR 0017](adr/0017-qotom-kernel-copy-roots.md#production-bound-root-construction-checkpoint).

On the Qotom the two subjects are separated in time, not in address space.
The q35 `dhcp-subject` image gives each its own address space. None of this
has run on the hardware yet.

### Maintainer steps for the DHCP-subject capture

Run these on the development host in a checkout of the merged branch, with
the `<flag set>` of
`hardware/lab/observations/qotom-device-stream-20261007/manifest.json`, as in
[Maintainer steps for the capture](#maintainer-steps-for-the-capture). The
board boots legacy BIOS.

1. Build the canonical inputs:

   ```sh
   ./scripts/build-image.sh
   ```

2. Run the keyless smoke test first. The program touches no Broadcom
   register (the only Broadcom store is the assignment variant's PMCSR
   write). It feeds the 17 q35 records through the real Qotom path: the copy roots,
   IPC, the DHCP subject, the scrub and the echo subject.

   ```sh
   .lake/build/bin/leanos-wifi-gen net-bcm-dhcp build/net/net-bcm-dhcp.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/net/net-bcm-dhcp.bin --ipc-device-stream \
     --network-subject --dhcp-subject
   scp build/qotom-wifi-lab/leanos-qotom-lab.elf freebsd@192.168.6.21:/var/tmp/leanos-wifi.elf
   sha256sum build/qotom-wifi-lab/leanos-qotom-lab.elf
   ssh freebsd@192.168.6.21 sudo sh /var/tmp/install-ssd.sh <sha256>
   build/wifi/lab-trial.sh build/wifi/dhcp556-smoke
   ```

   Expect the following in `build/wifi/dhcp556-smoke/cycle-1/serial.raw`:
   * the `BROADCOM-ASSIGN profile=qotom-j1900-pci-trust-v1-bcm43224-assign-v1
     ... admitted=1` record and `SERVICE grant subject=1 ... bind=accepted`,
     as in step 2 of the issue #450 steps;
   * 17 `NET event=deliver` records, the first of 6 bytes;
   * `NET event=handoff from=dhcp-subject to=echo-subject frame=11
     lease=10.0.2.16 scrubbed=8192`, then `IPC event=deliver receiver=1
     endpoint=13 role=echo-subject payload=lease`;
   * `WIFI 5101`/`5102` records from the frame source: every frame matched
     the reference;
   * `LEANOS/10 FINAL status=PASS dhcp-subject=1 echo-subject=1
     device-holder=2 dhcp-frames=11 lease=10.0.2.16 frames=17 fetches=17
     replies=8 refusals=4`.

3. Run the WiFi capture. The image embeds the PMK: keep it under `build/`,
   never commit it, and never print the passphrase. Do not set
   `LEANOS_WIFI_DHCP` or `LEANOS_WIFI_DRIVER_DHCP`: the driver must lease
   nothing. Keep the serve window at most 45 seconds. The lab watchdog is
   armed for 120 ticks and the join takes about 55 seconds. DHCP now runs
   inside the serve window.

   ```sh
   LEANOS_WIFI_PSK="$(cat ~/.config/leanos/wifi-psk)" \
     LEANOS_WIFI_SERVE_SECONDS=45 LEANOS_WIFI_NETWORK_SUBJECT=1 \
     .lake/build/bin/leanos-wifi-gen connect build/wifi/dhcp556.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/wifi/dhcp556.bin --ipc-device-stream \
     --network-subject --dhcp-subject
   ```

   Install it as in step 2 and start `build/wifi/lab-trial.sh
   build/wifi/dhcp556`. Expect `WIFI 0F17` (the link-only endpoint is up),
   then the DHCP subject's DISCOVER and REQUEST as `NET event=send` records
   and `WIFI 0F13` transmissions. Once `NET event=handoff ... lease=<leased
   address>` appears, run these from a LAN host:

   ```sh
   ping -c 10 <leased address>
   printf 'ring 3 echo\n' | nc -u -w 2 <leased address> 7
   ```

   Optionally record the air side with `sudo tcpdump -i eno1 'port 67 or
   port 68 or host <leased address>'`. Expect:
   * the DHCP exchange on the wire, with the Qotom's hardware address as
     the client identifier;
   * echo replies, with losses only on the radio link;
   * the UDP payload echoed back;
   * a final `LEANOS/10 FINAL status=PASS dhcp-subject=1 echo-subject=1 ...`
     with the leased address.

   If the box resets before `FINAL`, shorten the serve window; never
   lengthen it past 45 seconds without a long-session image ([Long
   sessions](#long-sessions)). The retained serial stream contains
   decrypted payloads. Redact them before committing an observation, and
   never commit `dhcp556.bin`.

## Group-key rotation (issue #557)

An access point rotates its group temporal key (GTK) on a fixed interval,
often an hour. It sends each station an EAPOL-Key group message 1,
protected with the station's TK, that carries the new GTK (wrapped with the
KEK), an EAPOL replay counter and the new key's Key RSC; the station answers
with group message 2. The new key alternates between key ids 1 and 2.

The driver keeps this exchange to itself. Both the ring-0 responder and the
frame endpoint use the same code (`LeanOS.Wifi.Responder.respond.groupKey`
inside `LeanOS.Wifi.Endpoint.handleFrame`):

* a message 1 is accepted only with a replay counter above the last one and
  a valid MIC (KCK), which then advances the counter;
* its key data is unwrapped with the KEK; a GTK KDE with key id 1–3 is
  installed (`Handshake.installGtk` refuses key id 0, the TK's);
* the new key's packet-number floor is the message's Key RSC, so a group
  frame under it is accepted only with a larger PN (as FreeBSD's net80211
  seeds `wk_keyrsc`);
* message 2 (MIC | secure, the same replay counter) is sent;
* the driver keeps one GTK: from then on a frame under the previous key id
  is dropped, and so is one under stale material for the new key id.

Records: `WIFI 0d05` (a GTK installed; value: its key id, also printed for
the 4-way handshake's GTK), `WIFI 0f09` (message 2 sent; key id), `WIFI
0f0a` (a message 1 dropped: stale counter, bad MIC, no usable GTK), `WIFI
0f06` (a frame dropped as a replay) and `WIFI 0f18` (a group frame accepted;
its key id). The Qotom lab also renders `0d05` and `0f09` as `LEANOS-LAB/1
WIFI-GTK installed key-id=N` and `LEANOS-LAB/1 WIFI-GTK rekeyed msg2=sent
key-id=N`.

**Model.** `LeanOS.GtkRekey` models one received frame against the driver's
key state (claim SC-WIFI-GROUP-KEY-ROTATION, `wifi_group_key_rotation`):

* the EAPOL replay counter never decreases, and the counters answered with
  message 2 strictly increase across any number of rotations, so a message
  1 is answered at most once (`run_replay_mono`, `run_msg2_sorted`,
  `msg2_once`);
* an answered message 1 installs exactly its key, key id (never 0) and Key
  RSC (`msg2_installs`);
* after a rotation, a frame under the new key id and key above the Key RSC
  is delivered (`delivered_after_rekey`); a frame under the previous key id
  (`stale_id_dropped`), under stale material (`stale_material_dropped`) or
  at or below its key's floor (`replayed_pn_dropped`) is dropped and changes
  nothing; delivered packet numbers raise their key's floor (`deliver_pn`,
  `step_pnTk_mono`, `step_pnGtk_mono`).

**Tests.** `tests/WifiRekeySim.lean` (`leanos-wifi-rekeysim`) runs
`handleFrame` and `takeTx` in the simulator on 1920 random frames (rotations
1↔2↔3, retransmitted, stale and forged message 1s, key id 0, failed
unwraps, packet numbers around every floor and across the 32-bit boundary)
and requires the model's outcome for each frame and its key state after
each frame. It also runs the q35 frame source below. `tests/WifiResponderSim.lean`
covers the same exchange on the ring-0 responder.

**q35 scenario `gtk-rekey`.** The network-subject image with the frame
source `net-q35-rekey` (`LeanOS.Net.RekeySource`): the driver's own
`handleFrame` and `takeTx` run on the model's fifteen CCMP-protected frames
(`GtkRekey.scenario`, test keys), with the radio replaced by a check of
every transmitted MPDU against the reference library. The key rotates 1 → 2
→ 1; broadcast ARP under each new key and a unicast ping reach the ring-3
echo subject and are answered; the stale, replayed and forged frames are
dropped. See [network-subject.md](network-subject.md#the-gtk-rekey-scenario).
`net-bcm-rekey` is the same program for the Broadcom target: a keyless
smoke test of the rotation on the Qotom's `--network-subject` path.

### Long sessions

A rotation is observed only by a session longer than the access point's
rekey interval, while the lab watchdog resets the board 120 seconds after
GRUB arms it. `build-qotom-recovery-lab.py --long-session SECONDS` (with
`--dhcp-subject`) builds an image in which the kernel **reloads** that
watchdog while the WiFi driver subject makes progress. `SECONDS` is 1–3600
and should be the program's `LEANOS_WIFI_SERVE_SECONDS`, which
`leanos-wifi-gen` accepts up to 4294 (the serve window is measured in
microseconds of the TSF's low 32-bit word).

How it works (`hardware/lab/qotom-network-subject.c.inc`):

* GRUB arms the timer exactly as before: 120 TCO v3 ticks, only after its
  board and register checks, digest- and minute-bound, and stopped again if
  the image does not load ([qotom-watchdog-lab.md](qotom-watchdog-lab.md)).
* The kernel reloads on two kinds of driver record: the link record (the
  join and the 4-way handshake completed) and every 40th tick the endpoint
  yields (`LeanOS.Wifi.Endpoint.serveLink`: one tick per second of the
  radio's TSF time).
* Before each reload it reads TCO1_CNT and TCO_TMR and asks the generated
  check `leanos_qotom_watchdog_kick` (`LeanOS.QotomWatchdogKick.kickDecide`).
  The check admits a reload only if the timer is still exactly as GRUB left
  it (TCO1_CNT 0, TCO_TMR 120), the session's budget is not used up, and the
  record is the link record (first reload) or a tick at least 40 ticks after
  the last reload. The budget is `2 + ceil(SECONDS / 40)`
  (`QotomWatchdogKick.budgetOf`), at most 92.
* A reload is one 16-bit write of 1 to TCO_RLD (port `0x460`), as FreeBSD's
  `ichwd` reloads. The kernel writes no other watchdog register: the
  timeout, the halt bit, NO_REBOOT and SMI routing stay GRUB's.
* Once the check refuses for any reason but "not due", the kernel never
  reloads again and prints `WATCHDOG-KICK stopped reason=N`. Every reload
  prints `LEANOS-LAB/1 WATCHDOG-KICK n=K budget=B event=...`, and the final
  record adds `watchdog-kicks=K session-end=window|budget
  unsent-replies=0|1`.
* **The session ends at its budget** (issue #567). Before the kernel resumes
  the driver program for its next record, it asks the generated check
  `leanos_qotom_watchdog_session_end` (`QotomWatchdogKick.endDecide`). Once
  every reload in the budget has been made, the check ends the session. The
  kernel does not resume the driver again. It prints `WATCHDOG-KICK
  session-end reason=budget kicks=B budget=B`, then `FINAL ...
  session-end=budget`, and halts. A reply still waiting in the transmit
  slot is not sent, and `unsent-replies=1` reports it. A session whose serve
  window ends first prints `session-end=window`, as before.
* The driver program's step bound rises from 4·10¹⁰ to 4·10¹² for the long
  session (`LAB_DEV_STEP_LIMIT`); the serve window and the reload budget
  bound the session instead.

Why the session ends at the budget rather than at a larger budget. In the
hardware run of issue #567, a one-hour image spent all 92 reloads before its
serve window ended. The kernel printed `WATCHDOG-KICK stopped reason=2`, and
the board reset 128 seconds after the last reload with no `FINAL`. The
budget assumes about one tick per second of the serve window. But the
window and the ticks are both measured in the radio's TSF time, which is
the access point's clock: the station adopts the timestamps in its beacons,
so neither is under LeanOS's control. No allowance added to the budget would
cover a clock that the access point sets. A larger budget would also raise
the reviewed reset bound past 3 h 6 min, because a one-hour session's budget
is already the cap of 92. So the budget, the cap and the bound stay as
reviewed, and the kernel ends the session when the budget is spent:

* `endDecide_zero_iff`: the session is served on exactly while the budget is
  valid and not spent.
* `serving_never_exhausted` and `asked_never_exhausted`: while the session
  is served, and so for every decision the kernel asks in a session
  (`QotomWatchdogKick.serve`), the kick check never refuses for a spent or
  an invalid budget. `stopped reason=2` cannot come before `FINAL`.
* `serve_spent_ends`: the kernel turn after the last reload ends the
  session, without taking another record. `FINAL` therefore follows the
  last reload by one record's handling by the echo subject, well inside the
  120 seconds that reload gave.
* `serve_budget_end_spent`, `serve_kicks_le_budget` and `serve_kicks_le_cap`:
  a session ends at its budget only once the budget is spent, and never
  reloads more than its budget or `capKicks` times. `reset_bound` and
  `cap_reset_seconds` still apply unchanged.

A one-hour session normally makes about 88 reloads, because a tick follows
the previous one after slightly more than a second. Its budget of 92 covers
3640 ticks, so normal sessions still end at their serve window. Only a
session whose ticks outrun the budget is cut short, and it is cut short with
its `FINAL`.

Why the box still recovers to FreeBSD:

* **A LeanOS hang stops the reloads.** A tick reaches the kernel only when
  the executor ran the driver program, the radio's TSF advanced, the ring-3
  subject took the previous record (the kernel fails closed on an unfetched
  one) and the kernel's IPC path cycled. If the kernel hangs, faults or
  stops scheduling, or the driver, the radio or the subject stalls, no
  reload follows and the timer resets the board at most 120 seconds after
  the last one, into GRUB, which sees the consumed request and chains
  FreeBSD as in every protected run.
* **A run that keeps "progressing" is still bounded.** Reloads are at least
  40 ticks apart and at most the budget in number (`run_kicks_le_budget`,
  `run_kicks_le_cap`, `kick_needs_ticks`), and each comes before the running
  deadline, so the board resets at most `(budget + 1) · 120` seconds after
  GRUB's arm (`reset_bound`): 96 minutes for a 30-minute session
  (`session_1800_reset_seconds`), at most 3 h 6 min for any image
  (`cap_reset_seconds`).
* **A completed run resets as before.** When the serve window ends the
  driver program halts, the kernel prints `FINAL` and halts, and the board
  resets at most 120 seconds after the last reload. When the budget is spent
  first, the kernel ends the session itself, prints `FINAL` and halts, so
  the reset follows the last reload in the same way.
* **A timer GRUB did not arm is never reloaded** (`unarmed_never_kicked`,
  `changed_never_kicked`), so an unprotected boot is not turned into a
  protected-looking one.

What this does not cover: the reset path itself and the one-shot request's
durability across a watchdog reset, which the earlier protected trials
established ([qotom-watchdog-lab.md](qotom-watchdog-lab.md)); SMM firmware
reloading or disabling the timer (GRUB found TCO SMI disabled); the C around
the checks (the event classification, the two reads, the one write, and
ending the session), which is reviewed, not proved; and how long the echo
subject takes over the record after the last reload, which is not bounded
by a proof (if it hangs, no `FINAL` follows and the board resets as for any
hang).

`run-qotom-recovery-lab.py --long-session SECONDS` observes for `SECONDS +
120` seconds more than a normal run, raises the capture limit from 1 MiB to
64 MiB, and writes `cycle-N/watchdog-kicks.json` before the scenario
classification: the reloads numbered from 1, within the budget, each less
than 120 seconds after the previous one (or GRUB's arm), and the FreeBSD
chain at most 150 seconds after the last reload. It also records the
session's `outcome`:

* `final-window`: `FINAL` with `session-end=window`.
* `final-budget`: `FINAL` with `session-end=budget`, after the kernel's
  `session-end` record, with exactly the budget's reloads.
* `budget-exhausted-before-final`: no `FINAL`, and the budget was spent
  (every reload made, or a `stopped reason=2` refusal). This is the failure
  of issue #567.
* `no-final`: no `FINAL` for any other reason, for example a hang that the
  watchdog recovered.

The last two outcomes carry an `error` and fail the cycle after
`result.json` is written. A `FINAL` whose `watchdog-kicks` differs from the
reloads, a reload after `FINAL`, or a budget end that does not match its
`FINAL` makes the capture fail as malformed.

### Maintainer steps for the long-session capture

Run these on the development host in a checkout of the merged branch, with
the `<flag set>` of
`hardware/lab/observations/qotom-device-stream-20261007/manifest.json`. The
board boots legacy BIOS.

1. **Find the access point's GTK interval.** Look in the router's settings
   for "Group Key Update Interval", "GTK rekey interval" or "WPA group
   rekey" (seconds). If it is longer than an hour or disabled, set it to 600
   seconds for the trial and restore it afterwards. The session must be
   longer than the interval plus the join (about 55 seconds); with 600
   seconds, `S = 900` covers at least one rotation. If the interval is
   unknown, use `S = 3600`: the capture then shows it (step 6).

2. **Build the canonical inputs and run the keyless smoke test.** It feeds
   the q35 rotation frames through the real Qotom path (the
   `--network-subject` image, no `--dhcp-subject`) and touches no Broadcom
   register:

   ```sh
   ./scripts/build-image.sh
   .lake/build/bin/leanos-wifi-gen net-bcm-rekey build/net/net-bcm-rekey.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/net/net-bcm-rekey.bin --ipc-device-stream --network-subject
   ```

   Install and run it as in [Maintainer steps for the
   capture](#maintainer-steps-for-the-capture), step 2. Expect two
   `LEANOS-LAB/1 WIFI-GTK rekeyed msg2=sent` records (key ids 2, then 1),
   `WIFI 5105` for each of the fifteen frames (the key state matched the
   model), `WIFI 5103` for each transmitted MPDU (the reference matched),
   four `NET event=deliver` frames after the configuration record, and
   `FINAL status=PASS network-subject=1 ... frames=5 fetches=5 replies=4`.

3. **Build the long-session image.** The program embeds the PMK: keep it
   under `build/`, never commit it, never print the passphrase, and do not
   set `LEANOS_WIFI_DHCP` or `LEANOS_WIFI_DRIVER_DHCP`.

   ```sh
   S=900
   LEANOS_WIFI_PSK="$(cat ~/.config/leanos/wifi-psk)" \
     LEANOS_WIFI_SERVE_SECONDS=$S LEANOS_WIFI_NETWORK_SUBJECT=1 \
     .lake/build/bin/leanos-wifi-gen connect build/wifi/gtk557.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/wifi/gtk557.bin --ipc-device-stream \
     --network-subject --dhcp-subject --long-session $S
   ```

   `build/qotom-wifi-lab/manifest.json` records `long_session_seconds` and
   `watchdog_kick_budget` (`2 + ceil(S / 40)`, 25 for 900 seconds).

4. **Install and run it** with the runner's long-session mode (`lab-trial.sh`
   with `--long-session $S` added to its runner command):

   ```sh
   scp build/qotom-wifi-lab/leanos-qotom-lab.elf freebsd@192.168.6.21:/var/tmp/leanos-wifi.elf
   sha256sum build/qotom-wifi-lab/leanos-qotom-lab.elf
   ssh freebsd@192.168.6.21 sudo sh /var/tmp/install-ssd.sh <sha256>
   python3 scripts/run-qotom-recovery-lab.py --host freebsd@192.168.6.21 \
     --host-key-alias freebsd.lan --usb-serial <stick serial> \
     --serial-device <FTDI by-id path> \
     --elf build/qotom-wifi-lab/leanos-qotom-lab.elf --image-on-ssd \
     --output build/wifi/gtk557 --cycles 1 --scenario watchdog-leanos \
     --long-session $S
   ```

5. **Drive traffic from a LAN host for the whole session**, once `NET
   event=handoff ... lease=<leased address>` appears. Keep a slow ping
   running, and make the LAN host re-ask for the Qotom's hardware address
   every minute, so that broadcast ARP requests reach the Qotom under
   whichever GTK is current:

   ```sh
   ping -i 10 <leased address> &
   while sleep 60; do
     sudo ip neigh del <leased address> dev eno1
     ping -c 2 <leased address>
   done
   ```

   Optionally record the wired side with `sudo tcpdump -i eno1 'arp or icmp'`
   (the EAPOL exchange stays on the air and is not visible there).

6. **Read the capture.** In `build/wifi/gtk557/cycle-1/serial.raw`:
   * `WATCHDOG-ARMED ticks=120`, then `WATCHDOG-KICK n=1 budget=B
     event=link` once the link is up, then a reload about every 40 seconds
     (`event=ticks ticks=40`), and no `WATCHDOG-KICK stopped` before
     `FINAL`. If the budget was spent first, `WATCHDOG-KICK session-end
     reason=budget kicks=B budget=B` comes right after the last reload;
   * the 4-way handshake's `WIFI-GTK installed key-id=1` (or 2);
   * **the rotation**: `WIFI-GTK installed key-id=2` and the message 2
     transmit status (`WIFI 0e10`–`0e13`), then `WIFI-GTK rekeyed msg2=sent
     key-id=2`: group message 1 arrived and message 2 was sent;
   * **broadcast ARP under the new key answered**: after the rotation, `WIFI
     0f18 0x00000002` (a group frame accepted under key id 2), its `NET
     event=deliver`/`fetch`, the echo subject's 42-byte `NET event=send` and
     `WIFI 0f13 0x0000002a` (the ARP reply transmitted); no `WIFI 0f18`
     with the old key id after the rotation;
   * **ping still working**: ICMP `NET event=send` records and `WIFI 0f13`
     after the rotation, and on the LAN host echo replies whose timestamps
     follow it;
   * `FINAL status=PASS dhcp-subject=1 echo-subject=1 ... watchdog-kicks=K
     session-end=window unsent-replies=0` (or `session-end=budget` with
     `K = B`), then a reset at most 120 seconds after the last reload and the
     FreeBSD chain.

   `cycle-1/watchdog-kicks.json` must show no `error`, with `outcome`
   `final-window` or `final-budget`. The access point's
   interval is the time between consecutive rotations: list the GTK records
   with their capture times from `cycle-1/events.jsonl`, for example

   ```sh
   python3 - build/wifi/gtk557/cycle-1/events.jsonl <<'PY'
   import json, sys
   for line in open(sys.argv[1]):
       e = json.loads(line)
       for rec in bytes.fromhex(e['hex']).split(b'\n'):
           if b'WIFI-GTK' in rec:
               print(f"{e['elapsed']:9.1f}", rec.decode(errors='replace'))
   PY
   ```

   The first rotation after the join can come anywhere within one interval
   (the access point's timer does not start at our association); the gap
   between two rotations in one capture is the interval itself. If no
   `rekeyed` record appears, the interval is longer than the session:
   shorten it on the router and repeat.

The retained serial stream contains decrypted payloads: redact them before
committing an observation, and never commit `gtk557.bin`.
