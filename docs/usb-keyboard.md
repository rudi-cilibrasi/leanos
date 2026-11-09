# USB keyboard (lab)

LeanOS drives the Qotom's Intel Bay Trail xHCI controller (PCI 8086:0f35,
00:14.0) with a Lean-authored device program and reads a USB boot-protocol
keyboard. Like the WiFi driver ([wifi-driver.md](wifi-driver.md)), the driver
is written in the instruction-set DSL of `LeanOS/Wifi/Bytecode.lean` and runs
on the runtime-free generated executor (`LeanOS/Wifi/Exec.lean`, with the
hooks of `hardware/wifi/wifi-gen-exec.h`).

| Module | Contents |
| --- | --- |
| `LeanOS/Usb/Xhci.lean` | BIOS handoff (extended capability walk), controller reset and start, command/event rings, root port reset, Enable Slot / Address Device, control transfers |
| `LeanOS/Usb/Hid.lean` | Shared with the mouse: root port scan, USB 2.0 hub support (hub descriptor, port power, debounce and reset, the hub's and the device's slot contexts with route string and transaction translator; [usb-hub.md](usb-hub.md)), boot interface discovery by protocol, interrupt IN endpoint, HID boot protocol, timed session loop; the enumeration and interface discovery also serve mass storage |
| `LeanOS/Usb/Keyboard.lean` | Boot-keyboard program: LED sweep, US-layout decoding, the session's key records |

The boot-protocol mouse program (`LeanOS/Usb/Mouse.lean`) reuses everything
but the decoder; see [usb-mouse.md](usb-mouse.md). The mass-storage reader
(`LeanOS/Usb/MassStorage.lean`) reuses the controller, hub and enumeration
code; see [usb-mass-storage.md](usb-mass-storage.md). The hub handling
the three share, its records and its tests are in [usb-hub.md](usb-hub.md).

The executor gained what DMA-based controllers need: version-2 program
images that name their PCI target and register window (up to 64 KiB), a
`physAddr` instruction giving the bus address of scratch RAM, 256 KiB of
64 KiB-aligned scratch accessed through volatile pointers, and, in the lab
kernel, a generic runner for several programs in sequence
(`scripts/build-qotom-recovery-lab.py --lab-program PATH`, repeatable). The
lab kernel's scratch RAM is identity-mapped below 16 MiB, so its virtual
address is its DMA address. The FreeBSD development runner offers no DMA;
the keyboard program refuses to run there.

The program is admitted under the xHCI confinement policy
(`docs/device-program-confinement.md`), which admits DMA into scratch: its
address sinks (CRCR, DCBAAP, ERSTBA, ERDP) and its descriptor map (DCBAA,
scratchpad array, ERST entry, input-context dequeue pointers and the TRB
rings, `Xhci.descriptorMap`) only ever hold zero or scratch bus addresses
([ADR 0021](adr/0021-j1900-device-dma-destinations.md)).

## QEMU

The driver source is generated per controller through `Xhci.Layout`
(`bayTrail` for the Qotom, `qemu` for QEMU's `qemu-xhci`: CAPLENGTH, runtime
and doorbell offsets, and Bay Trail's configuration-space port routing).
`scripts/run-q35-device-lab.py` builds the `kbd-q35` program into the q35
device-lab kernel, boots it on QEMU q35 with a `qemu-xhci` at 00:02.0, a hub
on root port 1 and a USB keyboard behind it, types a string through QMP
`input-send-event`, and requires every character back as a `KBD key=`
record, in order. With `--service` the `kbd-q35-service` program yields each
key instead of printing it and runs through the lab device service
(ADR 0022): subject 1 is granted the controller, an ungranted subject is
denied, the driver runs in fixed step budgets with one key per yield, and
after revocation the former holder is denied. `scripts/check.sh` runs both,
then the mouse scenario ([usb-mouse.md](usb-mouse.md)) and the
mass-storage scenario ([usb-mass-storage.md](usb-mass-storage.md)), and
the hub scenarios, `--hub-port 8` among them: the keyboard on the hub's last
port, a decoy mouse on port 1 ([usb-hub.md](usb-hub.md)).

## Trying it

Build and install the image from FreeBSD's side, then boot it once under the
watchdog:

```sh
LEANOS_KBD_SECONDS=60 lake exe leanos-wifi-gen kbd build/wifi/kbd.bin
python3 scripts/build-qotom-recovery-lab.py --prepared-repo . \
  --lab-program build/wifi/kbd.bin
# copy build/qotom-wifi-lab/leanos-qotom-lab.elf to FreeBSD /var/tmp/leanos-wifi.elf
# FreeBSD: sh hardware/wifi/install-ssd.sh <elf-sha256>
python3 scripts/run-qotom-recovery-lab.py --image-on-ssd --scenario watchdog-leanos ...
```

About 3 s after LeanOS starts, the keyboard LEDs sweep (Num, Caps, Scroll,
all, off) and `LEANOS-LAB/1 KBD ready ... type-now` appears on COM1 and the
screen. For the session length, each new key press prints
`LEANOS-LAB/1 KBD key=<char>`; the session ends with the key count and
LeanOS then returns to FreeBSD through the usual recovery path.

Num Lock, Caps Lock and Scroll Lock (usages 0x53, 0x39, 0x47) each toggle a
lock bit instead of printing a key. Caps Lock inverts Shift for the letters
only, so Caps Lock with Shift gives lower case and digits ignore it. Each
change prints `LEANOS-LAB/1 KBD locks num=<0|1> caps=<0|1> scroll=<0|1>`
and is sent to the keyboard's LEDs: a boot keyboard does not light them
itself (HID 1.11 §B.1).

The SET_REPORT(Output) is queued on EP0 without waiting, because a control
transfer that waited could consume a key report's transfer event. The session
counts only its interrupt endpoint's events. A completed EP0 transfer prints
`LEANOS-LAB/1 HID control-done cc=<code>`, where 1 is Success.
`LEANOS_KBD_IDLE=125` makes the keyboard repeat its report every 500 ms, which
verifies the interrupt path without anyone typing.

Hardware evidence:
[qotom-usb-keyboard-20260927](../hardware/lab/observations/qotom-usb-keyboard-20260927/README.md)
(idle reports), and
[qotom-usb-20261108](../hardware/lab/observations/qotom-usb-20261108/README.md):
a person typed `Hi LeanOS!`, Enter and Backspace, and 14 keys came back with
Shift applied, through the hub code of [usb-hub.md](usb-hub.md). Caps Lock
then neither toggled nor lit its LED, which is what led to the lock keys
(issue #632).
Report decoding is checked by `lake exe leanos-usb-kbd-decode` (in `scripts/check.sh`),
lock keys included. `python3 scripts/run-q35-device-lab.py --locks` types
with Caps Lock presses through QEMU, and requires the case to flip, both lock
records, and a Success completion for each LED SET_REPORT.

Limitations: one level of hub ([usb-hub.md](usb-hub.md)), one boot keyboard, polling (no interrupts),
US layout, no key repeat, no USB 3 devices beyond port handling.
