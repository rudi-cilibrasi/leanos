# USB keyboard (lab)

LeanOS drives the Qotom's Intel Bay Trail xHCI controller (PCI 8086:0f35,
00:14.0) with a Lean-authored device program and reads a USB boot-protocol
keyboard. Like the WiFi driver ([wifi-driver.md](wifi-driver.md)), the driver
is written in the instruction-set DSL of `LeanOS/Wifi/Bytecode.lean` and runs
on the runtime-free executor `hardware/wifi/wifi-exec.h`.

| Module | Contents |
| --- | --- |
| `LeanOS/Usb/Xhci.lean` | BIOS handoff (extended capability walk), controller reset and start, command/event rings, root port reset, Enable Slot / Address Device, control transfers |
| `LeanOS/Usb/Keyboard.lean` | Root port scan, USB 2.0 hub support (hub descriptor, port power/reset, transaction translator), boot-keyboard interface discovery, interrupt IN endpoint, HID boot protocol, LED sweep, US-layout decoding, timed session |

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
after revocation the former holder is denied. `scripts/check.sh` runs both.

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
`LEANOS_KBD_IDLE=125` makes the keyboard repeat its report every 500 ms, which
verifies the interrupt path without anyone typing.

Hardware evidence:
[qotom-usb-keyboard-20260927](../hardware/lab/observations/qotom-usb-keyboard-20260927/README.md).
Report decoding is checked by `lake exe leanos-usb-kbd-decode`.

Limitations: one level of hub, one boot keyboard, polling (no interrupts),
US layout, no key repeat, no USB 3 devices beyond port handling.
