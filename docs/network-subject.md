# Ring-3 network subject

Issue #450 moves the WiFi responder out of the ring-0 device program. The
BCM43224 driver used to answer ARP, ICMP echo and UDP echo itself
(`LeanOS/Wifi/Responder.lean`). Now a separate ring-3 *network subject*
answers them. The driver subject keeps the device, the network key and the
DHCP client. The network subject holds no device capability and never sees a
key.

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

## Not covered

- The q35 frames come from a program, not from a radio.
- The protocol logic is checked against a Lean reference, not proved against
  an RFC model.
- The DHCP client stays in the driver program for this change. Moving it to
  its own subject is a follow-up.
- The legacy ring-0 responder (`LeanOS.Wifi.Responder.respond`, `connect`
  with `LEANOS_WIFI_SERVE_SECONDS` but no `LEANOS_WIFI_NETWORK_SUBJECT`)
  remains as the lab baseline until the Qotom capture of the ring-3 path
  replaces it.
