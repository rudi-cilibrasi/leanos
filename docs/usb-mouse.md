# USB mouse (lab)

Beside the USB keyboard ([usb-keyboard.md](usb-keyboard.md)), LeanOS reads a
USB boot-protocol mouse through a Lean device program on the xHCI controller.
It is written in the same instruction-set DSL (`LeanOS/Wifi/Bytecode.lean`),
runs on the same generated executor and shares all of the keyboard's
controller, hub and enumeration code; only the report decoder is its own.

| Module | Contents |
| --- | --- |
| `LeanOS/Usb/Hid.lean` | Shared with the keyboard: root port scan, USB 2.0 hub support ([usb-hub.md](usb-hub.md)), boot interface discovery by protocol, interrupt IN endpoint, SET_PROTOCOL(boot) and SET_IDLE, timed session loop |
| `LeanOS/Usb/Mouse.lean` | Boot mouse report decoding (buttons, signed dx and dy, optional wheel byte), `MOUSE` records, the `program` entry point |

The program accepts the first interface of class 3 (HID), subclass 1 (boot),
protocol 2 (mouse), on a device directly on a root port or behind one USB 2.0
hub; a device with no such interface, a boot keyboard for instance, is
addressed, passed over and its slot disabled again. It configures the device,
selects the boot protocol with no idle repeat (SET_IDLE 0, the HID 1.11
§7.2.4 recommendation for mice) and polls the interrupt IN endpoint for a
fixed session.

Each report is decoded per HID 1.11 appendix B.2: byte 0 the buttons (bit 0
left, bit 1 right, bit 2 middle; the other bits device-specific and passed
through), bytes 1 and 2 the X and Y displacement as signed bytes. The wheel
is byte 3 when the report has a fourth byte (its length is the endpoint's max
packet size less the transfer event's residual), else 0; a report shorter
than 3 bytes is dropped. A report that neither moves nor changes the buttons
is dropped as well; every other one becomes one record (an excerpt of the
QEMU scenario below):

```text
LEANOS-LAB/1 MOUSE ready vendor=0x0627 product=0x0001 move-now
LEANOS-LAB/1 MOUSE buttons=1 dx=40 dy=-7 wheel=0
LEANOS-LAB/1 MOUSE buttons=0 dx=-127 dy=0 wheel=0
LEANOS-LAB/1 MOUSE buttons=0 dx=0 dy=0 wheel=1
LEANOS-LAB/1 MOUSE reports=18
LEANOS-LAB/1 MOUSE session-end records=18
```

The program packs a record into one print word (buttons | dx << 8 | dy << 16
| wheel << 24, each motion field a two's-complement byte); the lab kernel's
print hook (`hardware/lab/qotom-wifi.c.inc`) renders it with signs. Report
decoding is checked in simulation by `lake exe leanos-usb-mouse-decode`.

## Generator targets and confinement

`leanos-wifi-gen mouse` builds the program for the Qotom's Bay Trail
controller and `leanos-wifi-gen mouse-q35` for QEMU's `qemu-xhci`;
`LEANOS_MOUSE_SECONDS` sets the session length (default 60 and 10 s). Both
images pass `DeviceProgramConfinement.admissible` under the existing xHCI
policies (`qotomXhciPolicy`, `q35XhciPolicy`), unchanged: the mouse touches
the same registers, address sinks and descriptor map as the keyboard
([device-program-confinement.md](device-program-confinement.md)).

## QEMU

`python3 scripts/run-q35-device-lab.py --mouse` builds `mouse-q35` into the
q35 device-lab kernel and boots it on QEMU q35 with a `qemu-xhci`, a hub on
root port 1 and a `usb-mouse` behind it. Once `MOUSE ready` appears, QMP
`input-send-event` moves the mouse (`rel` events on the x and y axes, one of
them beyond a report's 127 counts), presses and releases the left, right and
middle buttons (`btn` events, two buttons held at once) and turns the wheel
(`wheel-up` and `wheel-down`).

QEMU's mouse merges the motion that arrives between two polls into one report
and spreads motion beyond 127 counts over several, while it queues one report
per button state. The check is therefore on runs of consecutive records with
equal buttons: the runs' button states, in order, must be exactly the states
the button events produced, and each run's dx, dy and wheel must sum to the
motion sent while that state held. It also requires the ready record to name
QEMU's mouse (0627:0001), the session-end count to match the records, and the
program to end with status 0. `scripts/check.sh` runs it after the keyboard
scenarios.

`--mouse --keyboard-first` puts a `usb-kbd` on hub port 1 and the mouse on
port 2, so the driver passes over the keyboard's boot interface and addresses
the mouse in the driver context the keyboard used; it requires the keyboard to
be rejected and the same records, and `scripts/check.sh` runs it too, as
well as `--mouse --hub-port 5`: the mouse on hub port 5, a decoy keyboard
on port 1, with the hub records checked ([usb-hub.md](usb-hub.md)).

Known issue, shared with the keyboard, fixed in a3d0e3ec: the passed-over
device's EP0 TRBs kept the reused ring's cycle bit, so the controller replayed
its GET_DESCRIPTOR(configuration) after the next device's first request and
the ready record showed `vendor=0x0932 product=0x0004`; `Xhci.ringInit` now
clears every TRB's control dword.

On the Qotom the `mouse` image would be built and booted like the keyboard's
([usb-keyboard.md](usb-keyboard.md), "Trying it"), with
`LEANOS_MOUSE_SECONDS=60 lake exe leanos-wifi-gen mouse build/wifi/mouse.bin`
and `--lab-program build/wifi/mouse.bin`; it has not been run there yet.

The mass-storage reader shares the same enumeration with a different
interface match ([usb-mass-storage.md](usb-mass-storage.md)).

Not covered: hardware evidence, and a device-service (yield) form. Absolute
pointers (tablets), report-protocol features, more than one mouse and the
limitations of the shared enumeration (one level of hub, polling;
[usb-hub.md](usb-hub.md)) are out
of scope.
