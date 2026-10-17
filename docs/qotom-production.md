# Production Qotom network image

Issue #569 asks for a canonical Qotom image that boots stand-alone and needs
no recovery-lab harness. It runs the WiFi driver, the DHCP client and the
echo responder as three isolated ring-3 subjects. The lab images of
issues #450, #556 and #557 ran the same programs in a different shape:

| | Lab image | Production image |
| --- | --- | --- |
| Address spaces | Two; the DHCP and echo subjects take turns in A, with A's stack scrubbed at the hand-off | Three; the DHCP subject in A, the driver in B, the echo subject in C |
| Frame transport | The audited copy roots, 16 bytes per transfer, A's stack pages only | A copy window per port holder, a whole frame per transfer |
| Watchdog | Armed by GRUB; long sessions reload it | None |
| After `FINAL` | Reset after 30 s, back to FreeBSD | Absorbing halt with interrupts disabled |
| Composition | Opt-in flags, copied from a capture manifest | One fixed flag set (`scripts/build-qotom-production.py`) |

## Build

After the canonical build:

```sh
./scripts/build-image.sh
python3 scripts/build-qotom-production.py               # keyless net-bcm-dhcp program
python3 scripts/test-qotom-production-image.py
```

The ELF is `build/qotom-production/leanos-qotom-production.elf`. The
default device program is `net-bcm-dhcp`, the keyless smoke program, which
touches no Broadcom register. `--program IMAGE` takes another
`leanos-wifi-gen` image. A `connect` image built with
`LEANOS_WIFI_NETWORK_SUBJECT=1` embeds the PMK: keep it under `build/`,
never commit it, and never print the passphrase.

## What the image does

`scripts/build-qotom-production.py` drives
`scripts/build-qotom-recovery-lab.py` with one reviewed flag set and
`--production-network`. Nothing in the flag set is optional. The boot path,
in order:

1. Handoff, ACPI and ECAM. The bounded Multiboot2 handoff, the
   root-selected ACPI tables and the DSDT are captured and checked, and the
   ECAM reads are gated on the firmware tables.
2. PCI inventory and quarantine. The native PCI inventory and capability
   lists are read. Each controllable device then goes through its reviewed
   quarantine stage: EHCI, xHCI, AHCI, HDA, TXE, the root ports, the
   Realtek NIC, the Broadcom (to D3hot), and graphics.
3. PCI trust contract. The final PCI admission and the initial trust
   contract `qotom-j1900-pci-trust-v1` are applied
   ([ADR 0018](adr/0018-qotom-pci-initial-trust-contract.md)).
4. Isolation and platform admission. The rest of the path:
   - the no-SMAP control;
   - the closed and copy roots;
   - closed-root entry and return;
   - the blocking-IPC profile;
   - whole-platform admission `qotom-j1900-clbtm210-v2`
     ([ADR 0019](adr/0019-typed-platform-admission.md)).

   The admission's isolation input also covers root C and the four window
   roots.
5. Broadcom assignment. The reviewed variant
   `qotom-j1900-pci-trust-v1-bcm43224-assign-v1` returns the Broadcom to D0
   for an assignable program only
   ([ADR 0027](adr/0027-qotom-broadcom-assignment-contract.md)). The driver
   subject then binds the program.
6. Network profile. After the fixed first exchange of the blocking-IPC
   profile, the production network profile runs
   (`hardware/lab/qotom-production-network.c.inc`).

## Three subjects in three address spaces

| Subject | Model role (`LeanOS.DhcpSubject`) | Holds | Window |
| --- | --- | --- | --- |
| B (2) | driver (1) | the device capability for the bound program | none |
| A (1) | DHCP subject (2), `subjects/dhcp` | a frame port | A's two stack pages |
| C (3) | echo subject (3), `subjects/echo` | a frame port | C's stack page |

The image's boot object is assembled with the three-subject page tables
(`LEANOS_THREE_SUBJECT_SCENARIO`). Subject C's text and stack come from the
echo subject's object and an `entry.S` stack page
(`LEANOS_SUBJECT_C_OBJECT`). The generated boot page plan therefore has
three roots:

- C's pages are user pages in root C only, and absent from A's and B's
  roots;
- A's and B's pages are absent from root C.

The kernel checks every leaf of root C against that plan before any subject
runs. `scripts/test-qotom-production-image.py` checks the same separation
on the plan the build generated.

The copy-root inventory gains C's two pages, the third audited variant of
`LeanOS.QotomCopyRootPublication`:

- variant 2: eight protected frames, four removed, 4085 retained;
- `production_inventory_publishes`, `accepted_inventory_exact` and
  `variants_reject_each_others_inventory` cover it.

## Frames through copy windows

Every fetch and send goes through the caller's copy window
([frame-copy-window.md](frame-copy-window.md)):

- the decision is `leanos_frame_port_check`;
- the alias address is `leanos_frame_window_operand`;
- the move is `frame_window_transfer`, which returns to the closed root.

The window roots are built from A's boot root with the protected inventory
of all eight frames. They are checked leaf by leaf, and the closed root they
are built over must equal the published closed root. A's window spans two
pages, so its aliases use B's text page and B's stack page, both absent from
A's root. C's window uses B's text page.

The proved confinement of claim SC-FRAME-COPY-WINDOW carries over to these
copies:

- the window roots map no other subject's frame;
- an accepted copy refines `DhcpSubject.step`, so SC-DHCP-SUBJECT-SEPARATION
  applies;
- the generated operand agrees with the port witness.

## The lease signal

The DHCP subject hands its lease to the echo subject on endpoint 13. At
that moment, and at no other, the kernel stores 1 in the lease signal word
of the executor scratch, as the lab image and q35 do (issue #573,
`LeanOS.Net.FrameSource.leaseSignalAt`). The driver learns that the route moved,
never the address. A link-only `connect` program starts its serve window
then, so a slow DHCP server uses up the lease window, never the serve
window. The keyless `net-bcm-dhcp` program checks the word after every
record: 0 before the ACK, 1 from the ACK on.

## Records

The production image prints the lab image's records up to
`QOTOM-IPC-READY`, then these:

```text
LEANOS-LAB/1 MODE qotom-production final=halt watchdog=none
LEANOS-LAB/1 PRODUCTION-WINDOWS profile=qotom-network-v1 holders=1,3 a-window-pages=2 c-window-pages=1 fetch-root=writable send-root=read-only protected=8 roots=5 scan=exact operand=agree root-c=exact
LEANOS-LAB/1 PRODUCTION-READY profile=qotom-network-v1 subjects=3 address-spaces=3 frames=copy-window watchdog=none final=halt
LEANOS-LAB/1 NET event=deliver frame=1 bytes=6 port=dhcp
LEANOS-LAB/1 NET event=fetch subject=1 frame=1 bytes=6 copy=fetch-root model=accepted
LEANOS-LAB/1 NET event=handoff from=1 to=3 frame=13 lease=10.0.2.16 route=echo address-spaces=separate model=accepted
LEANOS/10 FINAL status=PASS profile=qotom-network-v1 subjects=3 dhcp-subject=1 echo-subject=3 device-holder=2 address-spaces=3 lease=10.0.2.16 frames=19 ...
```

The `MODE` record comes right after serial initialization. The window
record precedes the platform-admission record. These are the expected
records for the keyless program. The image has not run on the hardware.

## Checks

| Check | What it covers |
| --- | --- |
| `audit-qotom-blocking-ipc-integration.py --production-network` | The linked contract. A runs the DHCP subject; C's trampoline runs the echo subject; B is the driver loop. Only the first exchange uses the copy roots, and frames use the window transfer. The frame path checks the cyclic IPC, port, operand and device witnesses. Setup checks root C and builds the windows once each. Binding goes through the Broadcom assignment variant. No watchdog code. Eight mutations of this contract are rejected. |
| `audit-qotom-copy-root-publication.py --inventory production` | The linked inventory is variant 2: A's text two pages, eight protected frames, four removed |
| `scripts/test-qotom-production-image.py` | The three-root plan and its separation; both audits above; no reset or watchdog port, no lab watchdog or network-subject code; `finish` is the absorbing halt; the `MODE` record; the build manifest |
| `tests/qotom-copy-root-publication.c` | The generated publication check accepts each variant's counts only |
| `scripts/check-qotom-production-host.sh` | The dispatcher itself, compiled against stand-ins for the kernel and linked with the real generated witnesses, over a whole session (subsection below); then each of eight preconditions is broken once and the dispatcher must fail closed |

### The dispatcher, hosted

The production image cannot boot under QEMU, so
`tests/qotom-production-network-host.c` compiles
`qotom-production-network.c.inc` on the host and drives its dispatcher one
syscall at a time, as the three subjects issue them:

- C starts and waits for the lease; A starts and waits for a record;
- B's frame fetch is refused;
- the link record and an OFFER reach A, which answers each through its
  window;
- the ACK reaches A, which hands the lease to C, then parks;
- an ICMP request reaches C, which answers; the program ends.

The test checks every refusal reason, root switch, woken payload and window
copy byte, and the final record:

```text
LEANOS/10 FINAL status=PASS profile=qotom-network-v1 subjects=3 dhcp-subject=1 echo-subject=3 device-holder=2 address-spaces=3 lease=10.0.2.16 frames=4 dhcp-frames=3 echo-frames=1 fetches=4 sends=3 refusals=5 ipc-edges=22 window-copies=7
```

## Capturing a run on the Qotom

### How the image boots and recovers

The production image boots from the one-shot `leanos-<digest>` request of
the SSD GRUB configuration ([Booting the image from the
SSD](wifi-driver.md#booting-the-image-from-the-ssd)). That path verifies the
ELF's digest, as the lab path does, but it arms no watchdog. GRUB consumes
the request before it boots LeanOS.

The image halts after `FINAL`. It also stays down if anything stops it
earlier, since nothing resets it. **The maintainer power-cycles the board.**
GRUB then finds the request consumed and chains FreeBSD.

### The runner's production mode

`scripts/run-qotom-recovery-lab.py --production-seconds SECONDS` runs a
production image with `--scenario leanos`. The runner:

1. arms the one-shot request and reboots the board;
2. captures the serial line;
3. prints `POWER-CYCLE cycle=1` once `FINAL` appears (or `SECONDS` + 180
   seconds have passed);
4. waits up to 15 minutes for FreeBSD to come back;
5. checks the request was consumed, then classifies the capture with
   `classify_production`.

### What `classify_production` checks

The capture passes when it has all of these:

- the one-shot launch, and no `WATCHDOG` record;
- the `MODE qotom-production` record before any kernel output;
- these records in order:
  - `PRODUCTION-WINDOWS ... scan=exact operand=agree root-c=exact`;
  - `PLATFORM-ADMISSION ... status=PASS`;
  - `BROADCOM-ASSIGN ... status=0 ... admitted=1`;
  - the service grant;
  - `QOTOM-IPC-READY`;
  - `PRODUCTION-READY`;
  - the hand-off from A to C;
  - `SERVICE end ... status=0`;
- one `FINAL status=PASS profile=qotom-network-v1 ...` whose counts agree
  with the records:
  - `frames` and `fetches` with the numbered deliveries and fetches;
  - `sends` with the sends;
  - four refusals;
  - DHCP plus echo frames equal to all frames;
  - window copies equal to fetches plus sends;
  - IPC edges equal to 4 × frames + 6;
  - the hand-off's frame and lease equal to `dhcp-frames` and `lease`;
- at most one `WIFI-LEASE signalled` record, after the hand-off, and no
  `WIFI-LEASE window-over` record;
- quiet after `FINAL`, then the consumed request's default and the FreeBSD
  chain.

It also reports `lease_signalled_after_ms`, the time the link-only
endpoint saw the lease take (none for the keyless program), and
`echo_service_ms`: for each echo frame, the time from its
delivery record to the echo subject's reply record, as the serial line saw
them. At 38400 baud this is an upper bound on the time the image took, not a
round-trip time. The ping round-trip time is measured on the LAN host.

### Maintainer steps

Run these on the development host in a checkout of the merged branch, with
the maintainer at the board. Nothing here needs the watchdog scripts.

1. Build the canonical inputs, then the keyless smoke image, and check it:

   ```sh
   ./scripts/build-image.sh
   python3 scripts/build-qotom-production.py
   python3 scripts/test-qotom-production-image.py
   ```

2. Run the keyless smoke test. The program touches no Broadcom register: the
   only Broadcom store is the assignment variant's PMCSR write. It feeds the
   19 q35 DHCP-subject records through the real Qotom path:
   - three address spaces;
   - the copy windows;
   - IPC;
   - the DHCP subject in A and the echo subject in C.

   ```sh
   scp build/qotom-production/leanos-qotom-production.elf freebsd@192.168.6.21:/var/tmp/leanos-wifi.elf
   sha256sum build/qotom-production/leanos-qotom-production.elf
   ssh freebsd@192.168.6.21 sudo sh /var/tmp/install-ssd.sh <sha256>
   python3 scripts/run-qotom-recovery-lab.py --host freebsd@192.168.6.21 \
     --host-key-alias freebsd.lan --usb-serial <stick serial> \
     --serial-device <FTDI by-id path> \
     --elf build/qotom-production/leanos-qotom-production.elf --image-on-ssd \
     --output build/wifi/prod569-smoke --scenario leanos --production-seconds 120
   ```

   When the runner prints `POWER-CYCLE cycle=1`, power-cycle the board.
   Expect `PASS cycle=1`. `build/wifi/prod569-smoke/cycle-1/result.json`
   should show:

   - `lease` `10.0.2.16`;
   - `frames` 19;
   - `refusals` 4;
   - `window_copies` equal to fetches plus sends.

   Any `FINAL status=FAIL reason=...` names the check that refused. Keep
   that capture.

3. Run the WiFi capture. The image embeds the PMK:
   - keep it under `build/`;
   - never commit it;
   - never print the passphrase;
   - do not set `LEANOS_WIFI_DHCP` or `LEANOS_WIFI_DRIVER_DHCP`: the driver
     leases nothing.

   The link-only endpoint has two windows ([DHCP retransmission and the
   lease window](wifi-driver.md#dhcp-retransmission-and-the-lease-window-issue-573)):
   the lease window `L` from the link record, then the serve window `S`
   from the hand-off. No watchdog bounds the session, so their sum may be
   longer than the lab's 45 seconds. A minute leaves a slow DHCP server room
   to answer, and five minutes of service leave time to ping and to send UDP
   echo by hand.

   ```sh
   L=60 S=300
   LEANOS_WIFI_PSK="$(cat ~/.config/leanos/wifi-psk)" \
     LEANOS_WIFI_LEASE_SECONDS=$L LEANOS_WIFI_SERVE_SECONDS=$S \
     LEANOS_WIFI_NETWORK_SUBJECT=1 \
     .lake/build/bin/leanos-wifi-gen connect build/wifi/prod569.bin
   python3 scripts/build-qotom-production.py --program build/wifi/prod569.bin
   python3 scripts/test-qotom-production-image.py
   ```

   Install it as in step 2, then start the runner with `--output
   build/wifi/prod569 --production-seconds $((L + S + 120))`.

4. Drive traffic from a LAN host once `NET event=handoff ... lease=<leased
   address>` appears on the serial line (`WIFI 0F17` marks the link-only
   endpoint up before that, and `WIFI-LEASE signalled after-ms=<ms>` the
   start of the serve window after it):

   ```sh
   ping -c 20 <leased address> | tee build/wifi/prod569/ping.txt
   printf 'ring 3 echo\n' | nc -u -w 2 <leased address> 7
   ```

   Optionally record the wired side with `sudo tcpdump -i eno1 'port 67 or
   port 68 or host <leased address>'`. Expect:

   - the DHCP exchange on the wire, with the Qotom's hardware address;
   - echo replies, with losses only on the radio link;
   - the UDP payload echoed back.

5. When the serve window ends, the image prints `FINAL status=PASS
   profile=qotom-network-v1 ... lease=<leased address>` and halts. Power-cycle
   the board when the runner asks. Expect `PASS cycle=1`.

6. Report latency against the lab baseline. The lab image answered ping in
   about 125 ms through the 16-byte copy roots. The ring-0 responder of the
   2026-09-29 capture took 6.5 to 23.2 ms. Record:
   - `ping.txt`'s round-trip times (min/avg/max/mdev);
   - `result.json`'s `echo_service_ms` (frames, median, max).

7. Before committing an observation, redact the cycle ([Redacting a
   capture](wifi-driver.md#redacting-a-capture)): the serial stream holds
   decrypted payloads. Never commit `prod569.bin`.

If the board does not come back after the power cycle, recover it as for any
lab image. GRUB has already consumed the request, so its default boots
FreeBSD.

## Not covered

- The Qotom capture itself: a lease from the router, then ping and UDP
  echo answered by the echo subject, with latency against the lab's
  ~125 ms. It needs the maintainer at the board
  ([Maintainer steps](#maintainer-steps)).
- The image serves for at most the program's lease window plus its serve
  window, each at most 4294 seconds, then prints `FINAL` and halts. A power cycle returns the board to
  FreeBSD.
- The trusted premises of the PCI trust contract stay unproved (ADR 0018):
  posted-write drain, TXE-private quiescence, and firmware and SMM
  noninterference.
- The serial records keep the lab's `LEANOS-LAB/1` prefix.
