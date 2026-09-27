# LeanOS USB keyboard on the Qotom — 2026-09-27

LeanOS (lab kernel, image loaded from the SSD under the watchdog-protected
one-shot request) ran the Lean-authored xHCI keyboard program
`LeanOS/Usb/Keyboard.lean` on the Intel Bay Trail xHCI controller
(PCI 8086:0f35, 00:14.0). The keyboard, a Chicony 04f2:0402 low-speed boot
keyboard, is behind the board's Genesys 05e3:0610 high-speed hub.

Both runs show the same enumeration:

1. BIOS handoff through the USB legacy support capability found at 0x8460 by
   walking the extended capability list: `0x00010801` → `0x01000801`.
2. Controller reset and run with polled command and event rings; root port 4
   reset to a high-speed device.
3. Enable Slot / Address Device (slot 1) → device descriptor
   `05e3:0610`, class 9: hub. SET_CONFIGURATION, hub descriptor (4 ports),
   Configure Endpoint marking the slot as a hub, port power.
4. Hub port 3: connected, low speed; hub port reset → enabled. Slot 2
   addressed through the hub's transaction translator → `04f2:0402`.
5. Configuration descriptor parsed: boot keyboard interface 0, interrupt IN
   endpoint 0x81. SET_CONFIGURATION, Configure Endpoint, SET_PROTOCOL(boot),
   SET_IDLE, then SET_REPORT sweeping the Num, Caps and Scroll Lock LEDs.
6. `LEANOS-LAB/1 KBD ready vendor=0x04f2 product=0x0402 type-now`, then the
   typing session; typed keys appear as `LEANOS-LAB/1 KBD key=...` on COM1 and
   the screen.

- `idle-reports/`: 20 s session with SET_IDLE 500 ms, so the keyboard sends
  its (empty) report periodically without a key press. `KBD reports=40`:
  exactly the expected 40 interrupt IN transfers, establishing the interrupt
  data path end to end. ELF
  `09e81ddb35ecaab7d697ad7a0095868cab01cc7827530682e4f0f993d39fa6a7`, capture
  SHA256 `1419e1f5880364e099e39a4d427d16e9b6c54daee7265e23f35213819befba15`; FreeBSD SSH returned (boot epoch `1790531666` to
  `1790531908`).
- `typing-session/`: the normal image (SET_IDLE 0, report on change only)
  left installed for a person to type into: 60 s session, ready 3.3 s after
  the watchdog was armed, `keys=0` because nobody was at the keyboard. ELF
  `1036c962aede3b9b18e9fde285de68350051f10fada4f39b328c7ba91cfbb4ea`, capture
  SHA256 `79478dcf7cebee964fe37875eb97911fda5f6a6449546f0a09d115c16e5c8a1e`; FreeBSD SSH returned (boot epoch `1790531908` to
  `1790532188`).

Report decoding (new-key detection, Shift, US layout, rollover, Enter and
Backspace) is checked in simulation by `lake exe leanos-usb-kbd-decode`.
Not established on hardware: a physical key press (awaiting a person).
