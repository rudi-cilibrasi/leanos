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

### Lab runner results for device programs

The runner classifies a device-program capture (issue #572). It reads the lab
image's build manifest, `manifest.json` beside `--elf` (or `--lab-manifest
PATH`). An image built with `--ipc-device-stream` is a device program, and
the manifest's flags name its scenario:

* `qotom-device-stream`: `--ipc-device-stream` alone (the keyboard stream).
* `qotom-network-subject`: with `--network-subject`.
* `qotom-dhcp-subject`: with `--dhcp-subject`.
* A long session: with `--long-session`. The runner takes `SECONDS` and the
  reload budget from the manifest. A `--long-session` argument must agree
  with them.

The manifest records the image's `elf_sha256`. The runner refuses a manifest
that names a different ELF, or flags that the builder would refuse.

`classify_device_program` passes a capture only when all of these hold:

* The protected launch: the watchdog window, the single 120-tick arm, the
  digest-bound load and the recovery mode record.
* The scenario's records, in order:
  * `PLATFORM-ADMISSION ... status=PASS`;
  * for the network images, `BROADCOM-ASSIGN ... status=0 ... admitted=1`;
  * `SERVICE grant ... bind=accepted`;
  * `QOTOM-IPC-READY`;
  * for the DHCP subject, the `NET event=handoff` and the lease's IPC
    delivery, with the handoff's frame and lease equal to `FINAL`'s;
  * `SERVICE end ... status=0`, unless the session ended at its budget.
* One `FINAL status=PASS` in the scenario's exact form. Its counts must
  agree with the records:
  * `frames` and `fetches` with the numbered `NET event=deliver` records;
  * `replies` with `NET event=send`;
  * `refusals` with `NET event=refuse`;
  * `deliveries` with the stream's IPC deliveries.
* A long session's reloads, as in [Long sessions](#long-sessions), with the
  outcome `final-window` or `final-budget`.
* The recovery:
  * no bytes for at least 10 seconds after `FINAL`;
  * then the consumed request's default record and the FreeBSD chain, at
    most 150 seconds after the last reload or the arm;
  * the request verified consumed.

Any other capture is a FAIL, and the runner collects every failed check, not
only the first. For example, a capture that ends with `FINAL status=FAIL
reason=qotom-net-lease-count` and one whose long session ran out of reloads
both fail. `cycle-N/result.json` records the result:

* `status` (`PASS` or `FAIL`) and `failures`;
* the parsed `terminal`;
* the record counts;
* the long session's reloads and `long_session_outcome`;
* the GTK key ids installed and the rotations;
* the recovery timings.

The runner then exits non-zero on a FAIL and prints `PASS cycle=N` otherwise.
`watchdog-kicks.json` is still written before the classification.

An image built with a single `--lab-program` and no other stage runs the
program once at the lab kernel's CPU gate, between `WIFI-BEGIN` and
`WIFI-END`. Under `--scenario watchdog-leanos` the runner classifies its
capture with `classify_lab_program` (issue #595). The device the kernel
reports in `WIFI-BEGIN id=` names the program. The runner knows the records
of `rtl8168-arp` (`id=0x816810ec`), step 2 of the [maintainer
steps](net-rtl8168.md#maintainer-hardware-steps):

* the 23-record before dump (`4137` … `41e8`);
* `4004` with the link bit, one to three `400c` transmit statuses that the
  chip handed back, the router's address (`4007`/`4008`) and at least one
  frame (`4009`);
* no `400d` and no `400e`;
* the 23-record after dump (`4237` … `42e8`), with `4237` = 0, `423c` = 0
  and 9346CR (`4250`) bits 7:6 clear;
* `40ff` last, then `WIFI-END status=0`.

The capture also needs the protected launch, the lab kernel's own terminal
(`FINAL status=FAIL reason=qotom-platform-pending`, since this image never
admits the platform) and the same recovery as a device program. Each failed
check is named, for example `after-dump: missing 42e8`, `teardown: 400e: the
reset did not complete` or `after-command: 4237 = 0x0c, not 0: TE, RE or RST
still set`. `result.json` also holds both dumps, the router's address and
the frame count. A capture of any other program still stops the runner with
an error, after `recovery.json` is written, and is checked by hand.

### Redacting a capture

A WiFi capture can contain decrypted network payloads: the driver's dumps of
decapsulated frame bodies (`WIFI 0e24`, `WIFI 0e26`), which hold other
devices' LAN traffic. Redact a cycle before committing any of it:

```sh
python3 scripts/redact-qotom-capture.py build/wifi/dhcp556/cycle-1 <output directory>
```

The helper removes those lines from `serial.raw` and from the timed events.
It writes the redacted `events.jsonl` and `serial.raw`, plus
`redaction.json`, which holds the source and output hashes and the number of
lines removed. It fails if a payload line survives. Inspect the output
before committing it.

`--fragment` also drops the records the classifiers do not read (data
dumps, PCI observations, `WIFI` value records other than the `rtl8168-arp`
program's tags `40xx`–`42xx`, IPC block/send/dispatch and `NET
event=fetch`). It joins events less than a second apart and stores the
timing as `timing.tsv`. The runner's self-tests
(`scripts/test-qotom-recovery-capture.py`) run over such fragments of six
hardware captures, in `scripts/fixtures/qotom-device-captures/`:

* a network-subject smoke test with the Broadcom assignment;
* a WiFi DHCP-subject session;
* a `qotom-net-lease-count` failure;
* a long session that ended at its budget;
* a one-hour session that ran out of reloads before `FINAL`;
* an `rtl8168-arp` run (issue #577, 2026-10-19), wired Ethernet with no
  payload records.

Each fragment's `manifest.json` holds the image's scenario flags.

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
   committing an observation ([Redacting a capture](#redacting-a-capture)),
   and never commit `net450.bin`.

## DHCP subject on the Qotom

Issue #556 moves the DHCP client out of the driver
([network-subject.md](network-subject.md#dhcp-as-its-own-subject)). With
`LEANOS_WIFI_NETWORK_SUBJECT` and without `LEANOS_WIFI_DRIVER_DHCP`, the
`connect` program joins, runs the 4-way handshake, and then serves the
link-only endpoint (`LeanOS.Wifi.Endpoint.connectAndServeLink`):

* Its first record is the 6-byte link record, our hardware address. It
  chooses no IPv4 address, and `WIFI 0F17` marks the endpoint up.
* It yields every decapsulated data frame as Ethernet II, and a 1-byte tick
  after each second of TSF time. The DHCP subject counts the ticks for its
  RFC 2131 retransmission schedule.
* It transmits whatever frame the kernel leaves in its scratch.
* It serves two windows: a lease window, until the kernel signals that the
  DHCP subject handed its lease off, and then a serve window. See [DHCP
  retransmission and the lease
  window](#dhcp-retransmission-and-the-lease-window-issue-573).

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
   write). It feeds the 19 q35 records through the real Qotom path: the copy roots,
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
   * 19 `NET event=deliver` records, the first of 6 bytes;
   * `NET event=handoff from=dhcp-subject to=echo-subject frame=13
     lease=10.0.2.16 scrubbed=8192`, then `IPC event=deliver receiver=1
     endpoint=13 role=echo-subject payload=lease`;
   * `WIFI 5101`/`5102` records from the frame source: every frame matched
     the reference;
   * `WIFI 5106 0x0000000c`: the frame source found the lease signal word
     set after the thirteenth record (the ACK) and unset after every record
     before it, so the kernel wrote it at the hand-off (issue #573);
   * `LEANOS/10 FINAL status=PASS dhcp-subject=1 echo-subject=1
     device-holder=2 dhcp-frames=13 lease=10.0.2.16 frames=19 fetches=19
     replies=8 refusals=4`.

3. Run the WiFi capture. The image embeds the PMK: keep it under `build/`,
   never commit it, and never print the passphrase. Do not set
   `LEANOS_WIFI_DHCP` or `LEANOS_WIFI_DRIVER_DHCP`: the driver must lease
   nothing. Since issue #573 the program has a lease window
   (`LEANOS_WIFI_LEASE_SECONDS`, required) and a serve window that starts
   at the lease (`LEANOS_WIFI_SERVE_SECONDS`). Keep their sum at most 45
   seconds: the lab watchdog is armed for 120 ticks and the join takes
   about 55 seconds.

   ```sh
   LEANOS_WIFI_PSK="$(cat ~/.config/leanos/wifi-psk)" \
     LEANOS_WIFI_LEASE_SECONDS=25 LEANOS_WIFI_SERVE_SECONDS=20 \
     LEANOS_WIFI_NETWORK_SUBJECT=1 \
     .lake/build/bin/leanos-wifi-gen connect build/wifi/dhcp556.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/wifi/dhcp556.bin --ipc-device-stream \
     --network-subject --dhcp-subject
   ```

   Install it as in step 2 and start `build/wifi/lab-trial.sh
   build/wifi/dhcp556`. Expect `WIFI 0F17` (the link-only endpoint is up),
   then the DHCP subject's DISCOVER and REQUEST as `NET event=send` records
   and `WIFI 0F13` transmissions. Once `NET event=handoff ... lease=<leased
   address>` and `LEANOS-LAB/1 WIFI-LEASE signalled after-ms=<ms>` appear
   (the serve window starts there), run these from a LAN host:

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

   If no lease came within the lease window, the program records
   `WIFI-LEASE window-over without-lease window-ms=25000` and the run ends
   with `FINAL status=FAIL reason=qotom-net-lease-count`; give a slow
   server a longer lease window in a long-session image ([DHCP
   retransmission and the lease
   window](#dhcp-retransmission-and-the-lease-window-issue-573)). If the box
   resets before `FINAL`, shorten the windows; never let their sum exceed
   45 seconds without a long-session image ([Long
   sessions](#long-sessions)). The retained serial stream contains
   decrypted payloads. Redact them before committing an observation
   ([Redacting a capture](#redacting-a-capture)), and never commit
   `dhcp556.bin`.

## DHCP retransmission and the lease window (issue #573)

Two Qotom runs of issues #556 and #557 ended with `FINAL status=FAIL
reason=qotom-net-lease-count`. QUAIL's DHCP server did not answer 15
DISCOVERs within the 45-second serve window, and in another run the lease
took 30 frames. The DHCP subject then retransmitted on every third tick,
and the serve window had to cover the lease and the service. Issue #573
changes both.

### The retransmission schedule

The DHCP subject (`LeanOS.Net.DhcpClient`) retransmits on the schedule of
RFC 2131 section 4.1, counted in the driver's one-second ticks:

* The wait before retransmission `n` (from 0) is `4 · 2^n` ticks, capped at
  64: 4, 8, 16, 32, 64, 64, ….
* Each wait is randomized by ±1 tick. The subject has no random source, so
  the offset is derived from the transaction id and `n`
  (`retransmitDelay`), like the transaction id itself, a lab-grade choice.
* While selecting, the DISCOVER is retransmitted for ever. While requesting,
  the REQUEST is retransmitted twice; when the third REQUEST's wait ends,
  the client restarts from DISCOVER with the next transaction id (RFC 2131
  section 4.4.1).

The schedule is proved in `LeanOS/Net/DhcpClient.lean`:

* `backoffBase_toNat`, `backoffBase_rfc`, `retransmitDelay_bounds`,
  `retransmitDelay_range`: the waits are the RFC's, within ±1, and 3 to 65
  ticks long.
* `step_tick_buf`, `stepRecord_tick`: the client's `step` on a tick moves
  its timer registers exactly as the timer model `Timer.tick` says,
  transmits exactly when the model retransmits, and changes no other
  register.
* `run_silent`, `selecting_gap`, `requesting_gap`: after a transmission the
  client is silent for its wait less one tick and retransmits on the next.

`tests/NetDhcpVectors.lean` checks the client against an independent
statement of the RFC schedule, over many transaction ids, and the frames
against `Wifi.Dhcp`. The generated C is checked against the model on the
same vectors (`scripts/check-dhcp-subject-host.sh`).

### The lease window and the serve window

The driver runs no DHCP client and parses no DHCP. It learns of the lease
from a **lease signal**: at the hand-off the kernel stores 1 in the 32-bit
scratch word `LeanOS.Net.FrameSource.leaseSignalAt`, and it writes the word
at no other time. The word tells the driver that the route moved to the
echo subject, never the address. `LeanOS.DhcpSubject` proves that the
signal is set only by the DHCP subject's accepted hand-off, is never unset,
and is set exactly when the echo subject holds a lease
(`step_leaseSignal_set`, `step_leaseSignal_stays`,
`run_leaseSignal_iff_lease`).

The link-only endpoint (`LeanOS.Wifi.Endpoint.serveWith`) then serves two
windows, both in TSF time:

* the **lease window**, `LEANOS_WIFI_LEASE_SECONDS` from the link record;
* the **serve window**, `LEANOS_WIFI_SERVE_SECONDS` from the moment the
  serve loop sees the signal.

When the loop sees the signal it records `WIFI 0f19` with the microseconds
the lease took, which the lab prints as `LEANOS-LAB/1 WIFI-LEASE signalled
after-ms=<ms>`. If the lease window ends first it records `WIFI 0f1a`,
printed as `WIFI-LEASE window-over without-lease window-ms=<ms>`, and ends.
A session thus lasts at most the lease window plus the serve window, and a
slow server uses up only the lease window. `leanos-wifi-gen connect`
requires `LEANOS_WIFI_LEASE_SECONDS` (1–4294) for the link-only endpoint.
The issue #450 endpoint, whose driver leases the address before it serves,
keeps one window.

`tests/WifiLeaseWindowSim.lean` (`leanos-wifi-leasesim`) runs the serve
program in the simulator against a silent radio, with a harness in the
kernel's place that sets the signal at chosen times. It checks that the
serve window runs from the signal for its full length however late the
signal comes in the lease window, and that without a signal the program
ends at the lease window.

Short runs must still fit the 120-tick watchdog: keep the lease window
plus the serve window at most 45 seconds (25 + 20 in the steps above). For a
slower server use a long-session image ([Long sessions](#long-sessions))
with `--long-session` set to the sum: the kernel reloads the watchdog on
the ticks, and the budget-aware end of issue #567 still puts `FINAL` first.

### The `dhcp-backoff` scenario

The q35 `dhcp-backoff` image is the `dhcp-subject` image with the frame
source `net-q35-dhcp-backoff` (`LeanOS.Net.DhcpSource.backoffProgram`), a
server that answers late:

1. the link record draws a DISCOVER;
2. the client retransmits the DISCOVER after 4, 9 and 15 ticks (its waits
   of 4, 8 and 16 ticks ±1 for this transaction id);
3. after five more silent ticks the OFFER arrives and draws a REQUEST;
4. the client retransmits the REQUEST after 4 and 9 ticks;
5. after two more silent ticks the ACK arrives, and B hands the lease off;
6. the echo records follow, as in `dhcp-subject`.

The frame source places the ticks at the waits `retransmitDelay` names and
checks every frame against `Wifi.Dhcp`, so each retransmission must come on
exactly its tick and every other tick must draw nothing. It also checks
the lease signal word after every record. The kernel counts the ticks and
the frames sent on them. The exact transcript is
`scripts/expectations/dhcp-backoff.transcript`, which ends with

```text
FINAL status=PASS subjects=3 dhcp-subject=2 echo-subject=3 device-holder=1 frames=57 dhcp-frames=51 echo-frames=6 fetches=57 sends=10 checked=57 refusals=4 ipc-edges=234 lease-signal=1 ticks=48 retransmits=5
```

```sh
LEANOS_BOOT_SCENARIO=dhcp-backoff ./scripts/run-image.sh
```

The `dhcp-subject` scenario follows the same schedule: its retransmitted
DISCOVER now comes on the fifth tick, its first wait for the second
transaction id.

### Maintainer steps for the issue #573 confirmation

Run these on the development host in a checkout of the merged branch, with
the `<flag set>` of
`hardware/lab/observations/qotom-device-stream-20261007/manifest.json`. The
board boots legacy BIOS.

1. Run the keyless smoke test of [Maintainer steps for the DHCP-subject
   capture](#maintainer-steps-for-the-dhcp-subject-capture), step 2. Its
   `WIFI 5106 0x0000000c` record shows that the lab kernel sets the lease
   signal at the hand-off.

2. Run the short capture of that section's step 3, with
   `LEANOS_WIFI_LEASE_SECONDS=25 LEANOS_WIFI_SERVE_SECONDS=20`, and record
   the DHCP exchange: `sudo tcpdump -i eno1 -tttt 'port 67 or port 68'`.
   Expect:
   * DISCOVERs from the Qotom's hardware address about 4, 8 and 16 seconds
     apart (±1 second), not every 3 seconds, until the server answers;
   * `NET event=handoff ... lease=<leased address>`, then `WIFI-LEASE
     signalled after-ms=<ms>` with the lease time;
   * replies to `ping -c 10 <leased address>` for about 20 seconds after
     the lease, however long the lease took;
   * `FINAL status=PASS dhcp-subject=1 echo-subject=1 ...`.

3. If QUAIL's server needs longer than 25 seconds, give it a long lease
   window in a long-session image. Build the program as in [Maintainer
   steps for the long-session
   capture](#maintainer-steps-for-the-long-session-capture), step 3, with
   `L=120 S=60`, `LEANOS_WIFI_LEASE_SECONDS=$L LEANOS_WIFI_SERVE_SECONDS=$S`
   and `--long-session $((L + S))`, and run it as in step 4 there. Expect
   `WIFI-LEASE signalled after-ms=<ms>` with `ms` up to 120000, then about
   60 seconds of service, then `FINAL status=PASS ... session-end=window`.
   A lease that never comes ends with `WIFI-LEASE window-over` after 120
   seconds and `FINAL status=FAIL reason=qotom-net-lease-count`.

The retained serial stream contains decrypted payloads. Redact them before
committing an observation, and never commit the `connect` program.

## Production image (issue #569)

The production Qotom image runs the same driver program, the DHCP subject
and the echo subject without the recovery-lab harness:

* three ring-3 subjects, each in its own address space;
* frames through per-subject copy windows instead of the 16-byte copy roots;
* no watchdog;
* an absorbing halt after `FINAL`.

`scripts/build-qotom-production.py` builds it from one fixed composition of
the reviewed boot path. Its capture boots from the one-shot request and ends
with a power cycle by the maintainer. See
[qotom-production.md](qotom-production.md), which also holds the maintainer
steps for the capture.

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
and should be the program's `LEANOS_WIFI_LEASE_SECONDS` plus its
`LEANOS_WIFI_SERVE_SECONDS`, the most a session can last (issue #573).
`leanos-wifi-gen` accepts each up to 4294 (each window is measured in
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
   L=60 S=900
   LEANOS_WIFI_PSK="$(cat ~/.config/leanos/wifi-psk)" \
     LEANOS_WIFI_LEASE_SECONDS=$L LEANOS_WIFI_SERVE_SECONDS=$S \
     LEANOS_WIFI_NETWORK_SUBJECT=1 \
     .lake/build/bin/leanos-wifi-gen connect build/wifi/gtk557.bin
   python3 scripts/build-qotom-recovery-lab.py --prepared-repo . <flag set> \
     --lab-program build/wifi/gtk557.bin --ipc-device-stream \
     --network-subject --dhcp-subject --long-session $((L + S))
   ```

   `L` is the lease window and `S` the serve window after the lease ([DHCP
   retransmission and the lease
   window](#dhcp-retransmission-and-the-lease-window-issue-573)).
   `build/qotom-wifi-lab/manifest.json` records `long_session_seconds` and
   `watchdog_kick_budget` (`2 + ceil((L + S) / 40)`, 26 for 960 seconds).

4. **Install and run it** with the runner's long-session mode. The runner
   reads `SECONDS` from the image's manifest; `--long-session $((L + S))`
   must agree with it:

   ```sh
   scp build/qotom-wifi-lab/leanos-qotom-lab.elf freebsd@192.168.6.21:/var/tmp/leanos-wifi.elf
   sha256sum build/qotom-wifi-lab/leanos-qotom-lab.elf
   ssh freebsd@192.168.6.21 sudo sh /var/tmp/install-ssd.sh <sha256>
   python3 scripts/run-qotom-recovery-lab.py --host freebsd@192.168.6.21 \
     --host-key-alias freebsd.lan --usb-serial <stick serial> \
     --serial-device <FTDI by-id path> \
     --elf build/qotom-wifi-lab/leanos-qotom-lab.elf --image-on-ssd \
     --output build/wifi/gtk557 --cycles 1 --scenario watchdog-leanos \
     --long-session $((L + S))
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
   `final-window` or `final-budget`, and `cycle-1/result.json` must show
   `status` `PASS` ([Lab runner results for device
   programs](#lab-runner-results-for-device-programs)). The access point's
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
committing an observation ([Redacting a capture](#redacting-a-capture)), and
never commit `gtk557.bin`.
