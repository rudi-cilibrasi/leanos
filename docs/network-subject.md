# Ring-3 network subject

Issue #450 moves the WiFi responder out of the ring-0 device program. The
BCM43224 driver used to answer ARP, ICMP echo and UDP echo itself
(`LeanOS/Wifi/Responder.lean`). Now a separate ring-3 *network subject*
answers them. The driver subject keeps the device, the network key and, in
the issue #450 image, the DHCP client. The network subject holds no device
capability and never sees a key. Issue #556 then moves the DHCP client into
a ring-3 subject of its own: see [DHCP as its own subject](#dhcp-as-its-own-subject).

This page covers the design, the model, the generated code, and the q35
`network-subject` scenario. The scenario runs the whole path without WiFi
hardware. The Qotom lab path, and the steps for the hardware capture, are in
[wifi-driver.md](wifi-driver.md#ring-3-network-subject-on-the-qotom).

## Frame transport

The verified blocking IPC carries two words per message. An Ethernet frame is
42 to 1514 bytes. So the kernel copies frames, and IPC carries only a length:

1. The driver's device program leaves a received frame at `rxAt` in its
   executor scratch and yields the frame's length. The layout is
   `LeanOS.Net.FrameSource`'s (`rxAt` 0x3E000, `txAt` 0x3E800, `txLenAt`
   0x3F000).
2. The driver subject's invocation (syscall 60) returns the sequence number
   and the length. The driver subject never sees the frame's bytes.
3. The driver subject sends the length and the sequence number to the network
   subject on endpoint 12 (syscall 8).
4. The network subject asks the kernel to copy the frame into its own buffer
   (syscall 64). It computes the reply in place, and asks the kernel to copy
   the reply out to `txAt` (syscall 65).
5. At the driver subject's next invocation the device program takes the reply
   from `txAt` and transmits it.

The kernel accepts a copy only when all of these hold:

- the caller holds the frame endpoint (the network subject);
- the endpoint is in the right state: a frame waiting for a fetch, no reply
  waiting for a send;
- the length is a frame length (at most 1514 bytes; at least 14 for a
  reply);
- the whole buffer range lies inside the caller's own writable memory. On q35
  that is its stack page, mapped writable for it alone.

The first frame is the 10-byte host configuration record: the hardware
address and the IPv4 address the subject answers for. A length below 14 is
never an Ethernet frame.

The alternatives were to stream frames as IPC words (one exchange per 16
bytes, printed edge by edge) or to map a shared page. Both widen something:
the first makes every frame dozens of audited exchanges, and the second needs
a new mapping kind. The kernel copy reuses the existing SMAP user-copy window
on q35. On the Qotom it reuses the existing bounded copy roots, sixteen bytes
per transfer.

## The model

`LeanOS/NetworkSubject.lean` models the endpoint: the receive and transmit
slots, every subject's memory, and five transitions. `deliver` is the device
program yielding a frame, `fetch` and `send` are the copies, `transmit` is
the program taking the reply, and `write` is a subject's own store.

| Theorem | Statement |
| --- | --- |
| `nonholder_refused` | A fetch or send by any subject but the network subject is refused and changes nothing |
| `step_mem_changed`, `run_mem_outside_window` | Across any run, a byte its owner did not store changes only inside the network subject's window |
| `run_driver_mem` | The driver subject never receives a frame byte |
| `step_rx_changed` | The receive slot changes only when the device program delivers |
| `step_tx_changed` | The transmit slot changes only by the program taking it, or by an accepted send of exactly bytes of the network subject's window |
| `network_no_device_effects` | The network subject is never granted a device: every bind or invoke it attempts is denied without effect (`DeviceCapability.ungranted_subject_no_device_effects`) |
| `frameCopyCheck_fetch`, `frameCopyCheck_send`, `frameCopyCheck_nonholder` | The generated witness `leanos_frame_copy_check` accepts exactly what the model accepts and refuses every other subject |

`SecurityClaims.network_subject_confinement` restates these as claim
SC-NETWORK-SUBJECT-CONFINEMENT ([security-claims.md](security-claims.md)).

## The protocol logic is generated from Lean

`LeanOS/Net/Echo.lean` writes the responder once, generic over three hooks:
read a byte, write a byte, and hand on a value. It reads like
`LeanOS.Wifi.Exec.step`:

- At the C hooks (`LeanOS/Net/EchoC.lean`), `leanos_net_reply` is the
  compiled `reply`: allocation-free straight-line C with no loop, no
  recursion and no Lean runtime call.
- At the model hooks over a `ByteArray`, `replyFrame` is the reference.

The network subject, `subjects/net/main.c`, defines the hooks over its frame
buffer and includes the generated C. The build rule's `--generated` option
(`scripts/build-subject.sh`) compiles it in one translation unit, so the hooks
inline. The link keeps only what `subject_entry` reaches, and the policy check
still requires no undefined symbol. The generated responder adds about
1.8 KiB to the subject's 4 KiB text page.

`scripts/check-network-subject-host.sh` is the hosted generated-boundary row
`network-subject`. It does two things:

1. It requires `replyFrame` to agree with replies built independently from
   the frame constructors (`tests/NetEchoVectors.lean`).
2. It runs the generated C over 810 vectors, the frame source's frames with
   single-byte corruptions of every header byte and truncations, against
   `replyFrame` (`tests/net-echo-host.c`). It also checks the copy witness on
   fixed requests.

## The `network-subject` scenario

The image is the three-subject image with C built from `subjects/net`:

- **A**, the driver subject, holds the device capability for the frame source.
- **B** holds nothing.
- **C**, the network subject, holds the frame endpoint.

The frame source is the Lean device program `net-q35-frames`
(`LeanOS.Net.FrameSource`). It drives no device: its declared target is the
reserved identity `0xffffffff`, and its policy, `q35FrameSourcePolicy`,
admits no configuration access and no DMA. The kernel's MMIO and
configuration hooks fail-stop.

It yields six synthesized frames after the configuration record:

1. an ARP request for the host (padded to 60 bytes);
2. an ICMP echo request;
3. a UDP datagram to port 7;
4. a UDP datagram to port 9;
5. an ARP request for another address;
6. an ICMP echo request to another hardware address.

The first three draw replies. At its next invocation the program checks C's
reply, byte for byte, against `Echo.replyFrame` (or checks that there is no
reply), and prints one `NET event=checked` record per frame.

The kernel checks these too:

- its device table, at boot and on every device request, against
  `leanos_device_authorize`;
- its endpoint table, at boot and on every copy, against
  `leanos_frame_copy_check`;
- every frame exchange against `leanos_blocking_ipc_event`, with C in the
  model's receiver role.

Three requests are refused: C's device invocation, B's fetch and A's fetch.
The final record counts frames, fetches, replies, checks, refusals and IPC
edges. The exact transcript is
`scripts/expectations/network-subject.transcript`.

```sh
LEANOS_BOOT_SCENARIO=network-subject ./scripts/run-image.sh
```

## The `gtk-rekey` scenario

Issue #557 keeps a session alive across the access point's group-key
rotation. The driver handles the rotation itself, and the network subject
must keep receiving broadcast frames under each new key
([wifi-driver.md](wifi-driver.md#group-key-rotation-issue-557)). The
`gtk-rekey` image is the `network-subject` image with another frame source,
`net-q35-rekey` (`LeanOS.Net.RekeySource`). It drives no device either, but
it does not make up Ethernet frames: it runs the BCM43224 driver's own
receive path (`LeanOS.Wifi.Endpoint.handleFrame`) on CCMP-protected 802.11
frames and its transmit path (`Endpoint.takeTx`) on C's replies. Only the
radio is replaced: a frame is stored where the receive FIFO would leave it,
and every MPDU the driver transmits is compared with the one the reference
library builds.

The frames are the model's scenario (`LeanOS.GtkRekey.scenario`) under test
keys:

1. a broadcast ARP request under the first GTK (key id 1), delivered;
2. group message 1 rotating to key id 2 (replay counter 3, Key RSC 4),
   answered with message 2;
3. a broadcast under the retired key id 1, a broadcast at the new key's Key
   RSC, and (after the next frame) the same broadcast replayed: dropped;
4. a broadcast ARP request under key id 2, delivered;
5. message 1 retransmitted with the same counter, and one with a bad MIC:
   dropped;
6. a unicast ICMP echo request under the TK, delivered;
7. group message 1 rotating back to key id 1 with a third GTK, answered;
8. broadcasts under the old key-id-1 material and the retired key id 2:
   dropped;
9. a broadcast ARP request under the third GTK, delivered;
10. message 1 for key id 0 (the counter advances, nothing is installed),
    then one with that counter again: dropped.

For every frame the program checks the outcome the model gives
(`GtkRekey.scenario_outcomes`: delivered, answered with message 2, or
dropped) and, afterwards, the driver's whole key state (key id, GTK, TK,
replay counter, both packet-number floors). For every delivered frame it
checks C's reply against `Echo.replyFrame` and the protected MPDU the driver
transmits for it against the reference. The kernel logs the driver's
records as `NET event=driver` lines; the four delivered frames, the
configuration record and the kernel's checks are those of the
`network-subject` scenario. The final record adds the frames checked against
the model (`mpdus=15`), the rotations (`rekeys=2`), the frames rightly not
delivered (`not-delivered=11`) and the MPDUs matched (`transmitted=6`). The
exact transcript is `scripts/expectations/gtk-rekey.transcript`.

```sh
LEANOS_BOOT_SCENARIO=gtk-rekey ./scripts/run-image.sh
```

## DHCP as its own subject

In the `network-subject` image the driver leases the address and tells the
network subject in the configuration record, so the driver chooses the
address the network subject answers for. Issue #556 takes that policy out of
the driver. Three ring-3 subjects share the frame endpoint:

- **A**, the driver subject, holds the device capability. Its program keeps
  the PMK and the frame transport and nothing else. It never yields an
  address. Its first record is the 6-byte **link record**, the hardware
  address. It also yields a 1-byte **tick** after each second of TSF time
  (`LeanOS.Wifi.Endpoint.serveLink`).
- **B**, the DHCP subject (`subjects/dhcp`), holds one frame port. It runs
  the DHCP client: DISCOVER, OFFER, REQUEST, ACK and NAK, with a
  retransmission on every third tick without an answer.
- **C**, the echo subject (`subjects/echo`), holds another frame port. It is
  the network subject's responder (`leanos_net_reply`), but it takes its
  address only from the DHCP subject.

Each port has its own window: the holder's own stack page. The endpoint
serves one port at a time, its *route*. It serves B's port until B has a
lease. B then **hands the lease off** to C over endpoint 13, as two IPC words:
the hardware address and the leased IPv4 address. From then on the kernel
delivers every record to C, and B's next receive never returns.

### The client logic is generated from Lean

`LeanOS/Net/DhcpClient.lean` writes the client once, generic over the frame
hooks of `LeanOS.Net.Echo` and two register hooks, in the same token
discipline. It builds exactly the packets of `LeanOS.Wifi.Dhcp` (`discover`
and `request`) inside an Ethernet header. It parses replies with the checks
of `Wifi.Dhcp.parseReply`: IPv4 version, header length and checksum, no
fragment, UDP from port 67 to port 68, BOOTREPLY, the magic cookie and
well-formed options. It then follows `Wifi.Dhcp.Client.handle`.

`leanos_dhcp_step` (`LeanOS/Net/DhcpClientC.lean`) is the generated C. It
makes no allocation and no runtime call. Its only loops are the bounded zero
fill, the header checksum and the option scan. `subjects/dhcp/main.c`
defines the five hooks over its own frame buffer and registers, and includes
it (`--generated NetDhcp`). The client is about 3.5 KiB of the 4 KiB text
page.

`scripts/check-dhcp-subject-host.sh` is the hosted generated-boundary row
`dhcp-subject`. It does two things:

1. `tests/NetDhcpVectors.lean` requires the model reading to send exactly
   `Wifi.Dhcp`'s frames on the frame source's records. It also requires the
   model to agree with `Wifi.Dhcp.Client.handle` on 12818 OFFER, ACK and NAK
   variants, from both waiting states. The variants are single-byte
   corruptions of every byte and truncations. On ticks it requires the
   RFC 2131 retransmission schedule (issue #573,
   [wifi-driver.md](wifi-driver.md#dhcp-retransmission-and-the-lease-window-issue-573)).
2. `tests/net-dhcp-host.c` runs the generated C over the same vectors
   against the model. It checks the frame sent, the registers, and that no
   byte past the record or the frame is touched. It also checks the port
   witness on fixed requests.

### The shared-endpoint model

`LeanOS/DhcpSubject.lean` models the shared endpoint: both windows, the
route, the echo subject's lease, and six transitions. They are `deliver`,
`fetch`, `send`, `transmit`, `write` and the lease `handoff`.

| Theorem | Statement |
| --- | --- |
| `nonholder_refused`, `driver_refused` | A fetch or send by a subject holding no port, the driver included, is refused and changes nothing |
| `unrouted_refused` | A fetch or send by the port holder the endpoint does not serve is refused and changes nothing |
| `step_mem_changed`, `run_mem_outside_windows`, `run_driver_mem`, `run_port_holder_mem` | Across any run, a byte its owner did not store changes only inside that owner's own window |
| `step_tx_changed` | The transmit slot changes only by the program taking it, or by the routed holder's accepted send of exactly bytes of its own window |
| `handoff_refused`, `step_lease_changed`, `step_route_changed` | Only the DHCP subject can hand a lease off, and only while it is served; the echo subject's lease is exactly what it handed |
| `run_routed_leased`, `echo_fetch_leased` | From boot, the endpoint serves the echo subject only once it holds a lease |
| `leaseSignal_boot`, `step_leaseSignal_set`, `step_leaseSignal_stays`, `run_leaseSignal_iff_lease` | The one-bit lease signal the driver reads (issue #573) is set only by the DHCP subject's accepted hand-off, never unset, and set exactly when the echo subject holds a lease |
| `replyFrame_for_ip`, `echo_answers_only_lease` | The responder answers a frame only when the frame asks for the address it is given; so the echo subject answers only for the lease |
| `dhcp_no_device_effects`, `echo_no_device_effects`, `deviceAuthorize_ports` | Neither subject is granted a device; every bind or invoke either attempts is denied without effect |
| `framePortCheck_own_window`, `framePortCheck_nonholder`, `framePortCheck_fetch`, `framePortCheck_send` | The generated witness `leanos_frame_port_check` admits only a port holder, only for a window labelled its own, only while it is served, and accepts exactly what the model accepts |

`SecurityClaims.dhcp_subject_separation` restates these as claim
SC-DHCP-SUBJECT-SEPARATION ([security-claims.md](security-claims.md)).

### The `dhcp-subject` scenario

The image is the three-subject image with B built from `subjects/dhcp` and C
from `subjects/echo`. B is a template slot here: boot.S omits its
handwritten B under `LEANOS_SUBJECT_B_OBJECT`, and the build rule takes
`--slot b`. A's frame source is the Lean device program `net-q35-dhcp`
(`LeanOS.Net.DhcpSource`). Like `net-q35-frames`, it drives no device. It
yields 19 records:

1. the link record, which draws a DISCOVER;
2. an OFFER for another transaction, which is ignored;
3. an OFFER of 10.0.2.15, which draws a REQUEST;
4. a NAK, which draws a DISCOVER with the next transaction id;
5. four ticks without an answer, then a fifth that draws a retransmitted
   DISCOVER: the client's first wait for this transaction id, 4 ticks ±1
   on the RFC 2131 schedule (issue #573);
6. an OFFER of 10.0.2.16 for another hardware address, which is ignored;
7. the OFFER of 10.0.2.16, which draws a REQUEST;
8. an ACK from another server, which is ignored;
9. the ACK. B is now bound and hands 10.0.2.16 off to C.

Then C gets:

- an ARP request, an ICMP echo request and a UDP datagram to port 7 for
  10.0.2.16, which draw replies;
- the same ARP and ICMP requests for 10.0.2.15, the NAKed address (the
  address the issue #450 fixture answered for), which draw none;
- a tick, which draws none.

At its next invocation the program checks every frame B or C sent, byte for
byte. Before the hand-off it checks them against `Wifi.Dhcp`. After it, it
checks them against `Echo.replyFrame` for the leased address. After every
record it also checks the lease signal word, which the kernel sets at the
hand-off (issue #573): unset until the ACK, set from then on.

The kernel checks these too:

- its device table against `leanos_device_authorize`;
- its port table at boot, and every copy, against `leanos_frame_port_check`.
  At boot, each holder is refused the other's window and the unrouted port;
- every exchange on endpoints 12 and 13 against `leanos_blocking_ipc_event`.

Four requests are refused: C's device invocation, C's fetch before the
hand-off (`not-routed`), B's device invocation, and A's fetch
(`not-holder`). The exact transcript is
`scripts/expectations/dhcp-subject.transcript`.

```sh
LEANOS_BOOT_SCENARIO=dhcp-subject ./scripts/run-image.sh
```

On the Qotom the same two subjects run in turn in subject A, the only slot
the audited copy roots alias. The kernel zeroes A's stack pages at the
hand-off and restarts A at the echo subject's entry
([wifi-driver.md](wifi-driver.md#dhcp-subject-on-the-qotom)).

### The `frame-window` scenario

Issue #569 replaces the copy roots for frame transport with a *copy
window* that needs no SMAP: per port holder, a fetch root and a send root
built from a closed root, which alias only that holder's window. The
`frame-window` image is the `dhcp-subject` image with every fetch and send
moved through those roots instead of the SMAP window
([frame-copy-window.md](frame-copy-window.md)). Its exact transcript is
`scripts/expectations/frame-window.transcript`.

```sh
LEANOS_BOOT_SCENARIO=frame-window ./scripts/run-image.sh
```

## Not covered

- The q35 frames come from a program, not from a radio.
- The protocol logic is checked against a Lean reference, not proved against
  an RFC model.
- In the `network-subject` image the DHCP client still runs in the driver
  program (`LEANOS_WIFI_DRIVER_DHCP`). The `dhcp-subject` image moves it to
  its own subject.
- The DHCP subject renews nothing. It takes one lease and hands it off; its
  transaction id is derived from the hardware address, a lab-grade choice.
- On the Qotom the DHCP subject and the echo subject are separated in time
  (a scrub of one slot), not in address space as on q35.
- The legacy ring-0 responder (`LeanOS.Wifi.Responder.respond`, `connect`
  with `LEANOS_WIFI_SERVE_SECONDS` but no `LEANOS_WIFI_NETWORK_SUBJECT`)
  remains as the lab baseline.
- The `gtk-rekey` frames are protected with test keys by a program; the
  driver program is tested, not proved, against the rotation model
  (`LeanOS.GtkRekey`), and the driver keeps one GTK, so frames the access
  point still sends under the previous key after a rotation are dropped.
  The Qotom long-session capture that shows a real rotation is pending.
