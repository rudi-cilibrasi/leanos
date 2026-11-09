# USB hubs (lab)

The USB device programs find their device either on an xHCI root port or
behind one USB 2.0 hub. The programs are the boot-protocol keyboard
([usb-keyboard.md](usb-keyboard.md)), the mouse
([usb-mouse.md](usb-mouse.md)) and the mass-storage reader
([usb-mass-storage.md](usb-mass-storage.md)). A hub may be a keyboard's
built-in hub (the Qotom's keyboard sits behind the board's Genesys
05e3:0610), a dock or a monitor's hub. All three programs share the hub
code in `LeanOS/Usb/Hid.lean`. It talks to the hub only through the hub's
control endpoint (EP0) and polls; it does not use the hub's status-change
endpoint.

| Module | Contents |
| --- | --- |
| `LeanOS/Usb/Xhci.lean` | Root port reset, Enable Slot / Address Device with a caller-supplied route string, speed, root port and TT word, control transfers |
| `LeanOS/Usb/Hid.lean` | `findHub` (the hub search on the root ports), `setupHub` (hub descriptor, the hub's slot context, port power), `findOnHub` (the port search: debounce, reset, speed, the device's slot context); the `HUB` records; `attachWith`, which runs them for every program |
| `hardware/lab/qotom-wifi.c.inc` | The lab kernel's print hook, which renders the `HUB` records |

## What the programs do

1. **Hub search.** Root ports 1–6 are probed in order and each connected
   port is reset. A SuperSpeed port (PORTSC speed 4 or more) is passed over
   without addressing its device. A USB 2.0 hub is never on one. The
   SuperSpeed half of a USB 3 hub is, and its hub descriptor (type 0x2A)
   and port status differ from a USB 2.0 hub's, so taking it as the hub
   would end the program at the hub descriptor request. Every other device
   is addressed in driver context 0 and its
   device descriptor is read. The first device with bDeviceClass 9 is the
   hub. The others are disabled again.
2. **Hub setup.** The program sends SET_CONFIGURATION(1) and reads the hub
   descriptor (type 0x29, 9 bytes): bNbrPorts, wHubCharacteristics and
   bPwrOn2PwrGood. A Configure Endpoint command then marks the slot as a
   hub (see [Slot contexts](#slot-contexts)). SET_FEATURE(PORT_POWER) goes
   to ports 1 to bNbrPorts, at most 15. Then the program waits for the
   ports to come up, before it reads any status:
   - 2 × bPwrOn2PwrGood ms, the hub's power-good time (USB 2.0 §11.23.2.1);
   - plus 100 ms, the time a device may take after that to signal attach
     (TSIGATT, USB 2.0 §7.1.7.3);
   - never less than 250 ms in all. That is the fixed wait of the earlier
     driver, the timing that ran on the Qotom's Genesys hub.

   The wait matters because the port search passes over a port whose first
   GET_STATUS shows no connection. A device that attached late would be
   missed. A hub that switches port power comes out of its reset with its
   ports off, so on real hardware every device attaches only after this
   PORT_POWER.
3. **Port search.** Ports 1 to bNbrPorts (at most 15) are searched in order:
   - **Connection.** A port whose GET_STATUS shows no connection is passed
     over.
   - **Debounce.** On a connected port the program reads GET_STATUS every
     25 ms. A connection change is cleared with
     CLEAR_FEATURE(C_PORT_CONNECTION) and restarts the count. The connection
     must hold for four reads in a row (100 ms, USB 2.0 §7.1.7.3), within
     80 reads (2 s).
   - **Reset.** SET_FEATURE(PORT_RESET), then GET_STATUS every 10 ms until
     C_PORT_RESET is set (at most 50 reads), then
     CLEAR_FEATURE(C_PORT_RESET). The port must then be enabled. After
     20 ms of reset recovery (USB 2.0 §7.1.7.5 asks for at least 10 ms), the
     device's speed comes from wPortStatus: bit 9 low, bit 10 high, else
     full.
   - **Giving up.** A port that fails one of these steps is recorded and
     passed over; the search goes on.
4. **The device.** It is addressed in driver context 1 with its own slot
   context (below), and its device descriptor is read. The program's
   acceptance routine then runs: a HID boot interface of the wanted
   protocol, or a bulk-only SCSI interface. A device it refuses has its slot
   disabled, and the search goes on with the next port. The device's
   Configure Endpoint command (`Hid.setupInterface`,
   `MassStorage.configure`) repeats the same slot fields.
5. **No device behind the hub.** If no device behind the hub is accepted
   (or there is no hub), the root ports are searched for one plugged in
   directly. The hub's own root port is skipped.

A hub class request that fails ends the program with the xHCI driver's
transfer fail code (0x7F07), like any other failed control transfer.

## Slot contexts

The fields this driver sets (xHCI 1.1 §6.2.2; dword and bits in parentheses):

| Field | The hub | A device behind the hub |
| --- | --- | --- |
| Route String (dw0 0–19) | 0 | the hub port: tier 1, bits 0–3 |
| Speed (dw0 20–23) | its root port's PORTSC speed | from wPortStatus |
| MTT (dw0 25) | 0 | 0 |
| Hub (dw0 26) | 1 | 0 |
| Context Entries (dw0 27–31) | 1 | 1, then the highest endpoint DCI |
| Root Hub Port Number (dw1 16–23) | its root port | the hub's root port |
| Number of Ports (dw1 24–31) | bNbrPorts | 0 |
| TT Hub Slot ID (dw2 0–7) | 0 | the hub's slot, if the device is full or low speed and the hub high speed; else 0 |
| TT Port Number (dw2 8–15) | 0 | the hub port, under the same condition; else 0 |
| TT Think Time (dw2 16–17) | wHubCharacteristics bits 5–6 if the hub is high speed; else 0 | 0 |

The hub's slot context goes in a Configure Endpoint command whose input
control context adds only the slot context (A0) and no endpoint. That is
the command Linux uses for this (`xhci_update_hub_device`) on hosts newer
than xHCI 0.95; older ones use Evaluate Context.

The TT fields name the high-speed hub whose transaction translator turns a
full- or low-speed device's transactions into split transactions. Behind a
full-speed hub, which QEMU's `usb-hub` is, no translator is involved, and
the fields stay 0. MTT stays 0 too: a multiple-TT hub runs a single TT until
its alternate setting 1 is selected, and this driver never selects it.

## Records

The programs print these records on COM1, one line each. The lab kernel's
print hook (`hardware/lab/qotom-wifi.c.inc`) renders tags 0x2400–0x2406 and
assembles the device record from two print words. `<dec>` is unsigned
decimal; hex is lower case; `<speed>` is `full`, `low`, `high` or `super`
(PORTSC speed IDs 1–4), or the number for any other value.

```text
LEANOS-LAB/1 HUB passed-over root-port=<dec> speed=<speed>
LEANOS-LAB/1 HUB found root-port=<dec> speed=<speed> slot=<dec>
LEANOS-LAB/1 HUB configured ports=<dec> power-on-wait-ms=<dec> tt-think-time=<dec>
LEANOS-LAB/1 HUB port=<dec> status=0x<4 hex> change=0x<2 hex>
LEANOS-LAB/1 HUB port=<dec> skipped=<reason>
LEANOS-LAB/1 HUB device route=0x<5 hex> speed=<speed> root-port=<dec> tt-slot=<dec> tt-port=<dec>
```

- `passed-over`: a SuperSpeed root port that the hub search did not
  address.
- `found`: the hub, its root port, its speed and its xHCI slot.
- `configured`: bNbrPorts, the power-on wait used in ms (2 ×
  (bPwrOn2PwrGood + 50), at least 250), and the TT think time (0–3, for 8,
  16, 24 or 32 FS bit times) in the hub's slot context.
- `port`, `status`: GET_STATUS of a hub port, wPortStatus and the low byte
  of wPortChange (USB 2.0 Tables 11-21 and 11-22). Each searched port gets
  one record when it is first read. A port whose device is addressed gets a
  second one after its reset, read before C_PORT_RESET is cleared.
- `port`, `skipped`: a connected port given up. The reason is `unstable`
  (the connection did not hold for 100 ms within 2 s), `reset-timeout` (no
  C_PORT_RESET within 500 ms) or `not-enabled` (the reset completed, but the
  port is not enabled).
- `device`: the slot context fields of the device about to be addressed:
  route string, speed and root port, plus TT Hub Slot ID and TT Port Number.

Two raw records of the shared enumeration remain: `WIFI 2013 0x<class>`, the
bDeviceClass of a device addressed on a root port, and `WIFI 2019 0x<port>`,
a device on that hub or root port that the program passed over.

## Tests

`lake exe leanos-usb-hub-slot` (in `scripts/check.sh`) checks the fields
QEMU cannot reach. It runs the program's own fragments (`hubPortSpeed`,
`hubTtFields`, `hubSlotContext`, `hubDescriptorLimits`) in the simulator.
The results must equal values written out from the specifications: the TT
word for full-, low- and high-speed devices behind high- and full-speed
hubs (among them the Qotom's case, a low-speed keyboard on port 3 of a
high-speed hub in slot 1, giving 0x0301), the hub's slot dwords at both
speeds, the speed decoding with change bits set, and the port and
power-on-wait limits.

`python3 scripts/run-q35-device-lab.py --hub-port N` runs a program in QEMU
q35 with `qemu-xhci`. The device under test sits on port N of a `usb-hub`.
A decoy sits on hub port 1: a mouse for the keyboard program, a keyboard
for the mouse and mass-storage programs. QEMU attaches the full-speed hub
to xHCI port 5.

The device's own checks are those of its scenario: every typed key, the
mouse runs, or every mass-storage record against the disk image. The
`HUB` records must show:

- the hub found on root port 5 at full speed, with 8 ports, a 250 ms
  power-on wait (the floor: QEMU's bPwrOn2PwrGood is at most 75) and no TT
  think time;
- a status record for each port from 1 to N, connected (and powered) only
  at 1 and N, and after the reset connected, enabled and full speed;
- both devices' slot contexts with the hub port as the route string, full
  speed, root port 5 and no TT fields;
- no port given up, and the decoy passed over.

`scripts/check.sh` runs the keyboard on hub port 8 (the last port), the
mouse on port 5 and the storage on port 7, all beyond the four ports the
search covered before. The scenarios without `--hub-port` stay as they
were: their device is on hub port 1 of a hub whose ports are always
powered. In `--msc --root-port` the SuperSpeed storage is on xHCI port 2,
which the hub search now passes over:

```text
LEANOS-LAB/1 HUB passed-over root-port=2 speed=super
```

An excerpt of the keyboard's `--hub-port 8` transcript (QEMU's hub also
sets C_PORT_ENABLE when a reset enables a port, hence `change=0x12`):

```text
LEANOS-LAB/1 HUB found root-port=5 speed=full slot=1
LEANOS-LAB/1 HUB configured ports=8 power-on-wait-ms=250 tt-think-time=0
LEANOS-LAB/1 HUB port=1 status=0x0101 change=0x01
LEANOS-LAB/1 HUB port=1 status=0x0103 change=0x12
LEANOS-LAB/1 HUB device route=0x00001 speed=full root-port=5 tt-slot=0 tt-port=0
LEANOS-LAB/1 HUB port=2 status=0x0100 change=0x00
LEANOS-LAB/1 HUB port=7 status=0x0100 change=0x00
LEANOS-LAB/1 HUB port=8 status=0x0101 change=0x01
LEANOS-LAB/1 HUB port=8 status=0x0103 change=0x12
LEANOS-LAB/1 HUB device route=0x00008 speed=full root-port=5 tt-slot=0 tt-port=0
LEANOS-LAB/1 KBD ready vendor=0x0627 product=0x0001 type-now
LEANOS-LAB/1 KBD key=h
LEANOS-LAB/1 KBD session-end keys=11
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

Ports 3–6 print the same record as port 2; the mouse on port 1 is passed
over (`WIFI 2019 0x00000001`, among the raw lines the excerpt leaves out).

## Confinement

No policy, descriptor map, lab profile or pin changed. The hub is
addressed and configured in driver context 0 and uses only its control
endpoint. That means the same EP0 ring, input context and output context
that the enumeration used for it before. The device behind it uses context
1, as before. No new register, address sink or DMA structure is involved.
The per-port code is now one run-time loop instead of four unrolled copies,
so the keyboard, mouse and mass-storage images are about 97 KB smaller.
All of them still pass `DeviceProgramConfinement.admissible` under
`qotomXhciPolicy` and `q35XhciPolicy`.

## Not covered

- **A high-speed hub.** QEMU's only hub is full speed. So the TT fields
  (full- or low-speed device behind a high-speed hub) and a high-speed hub's
  TT think time are checked only in simulation. The Qotom's 2026-09-27
  keyboard run
  ([observation](../hardware/lab/observations/qotom-usb-keyboard-20260927/README.md))
  went through a high-speed hub's TT. It used the earlier code, which put
  the same values in these fields for that case (hub slot | port << 8).
  This code has since run on the Qotom (2026-11-08,
  [observation](../hardware/lab/observations/qotom-usb-20261108/README.md)),
  with the Genesys hub on root port 4:
  - `HUB configured ports=4 power-on-wait-ms=250 tt-think-time=3`;
  - each port's status;
  - two low-speed devices behind its TT, a mouse on port 3
    (`tt-slot=1 tt-port=3`) and a keyboard on port 4 (`tt-port=4`), and a
    high-speed flash drive on port 3 in a later run (`tt-slot=0 tt-port=0`).

  A person typed through the keyboard, and the mass-storage program read the
  flash drive. So the port loop, the power-on wait, the debounce, the
  C_PORT_RESET wait, the hub's slot speed and the TT condition have run on a
  real high-speed hub.
- **More than one hub level.** A hub behind the hub is addressed like any
  device and passed over: it has no interface the programs accept. Only the
  first hub is used: a hub on another root port is passed over too.
- **SuperSpeed hubs.** A USB 3 hub's SuperSpeed half is passed over and its
  USB 2.0 half is used, so a SuperSpeed device behind a USB 3 hub (which
  connects only to the SuperSpeed half) is not found.
- **Port power.** In QEMU the hub's ports are powered before the program
  runs, so the power-on step, and the power-on wait's TSIGATT margin, are
  not tested there. SeaBIOS powers them
  during its own USB scan, and they still read powered after the
  controller reset, also with `usb-hub,port-power=on`. A control run made the
  point: in a copy of the `--hub-port 8` keyboard image, the
  SET_FEATURE(PORT_POWER) request was patched to SET_FEATURE(PORT_SUSPEND).
  That copy still found the keyboard, every port reading powered. The
  debounce and the C_PORT_RESET wait do run in QEMU. Its hub never bounces
  a connection, delays C_PORT_RESET or leaves a reset port disabled,
  though, so the `skipped=` paths are untested.
- **Multiple-TT operation, hot-plug and the status-change endpoint.** Ports
  are searched once, at enumeration, by polling. Over-current, suspend and
  port indicators are not handled.
- **Port ranges.** Hub ports past 15 (the route string's limit for one
  tier) and root ports past 6 are not searched. On qemu-xhci, ports 7 and 8
  are USB 2 ports.
- **EP0 max packet size.** The shared Address Device gives EP0 a max packet
  size of 8 at full and low speed, and 64 at high speed. 8 is right for
  every low-speed device (USB 2.0 requires it), and QEMU does not hold a
  device to it. Linux reads bMaxPacketSize0 first and then updates EP0 with
  Evaluate Context; this driver does not. So a full-speed device or hub with
  a larger bMaxPacketSize0 may fail its first descriptor read on real
  hardware. This
  applies on root ports too ([usb-mass-storage.md](usb-mass-storage.md)
  describes the SuperSpeed case).
