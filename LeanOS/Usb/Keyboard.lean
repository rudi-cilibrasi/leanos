import LeanOS.Usb.Hid

/-
USB keyboard for LeanOS: find a boot-protocol HID keyboard (directly on a
root port or behind one USB 2.0 hub), configure it and turn its reports into
characters for a bounded session. Controller, hub handling, enumeration and
the session loop are shared with the mouse (`LeanOS/Usb/Hid.lean`).

USB 2.0 chapter 9/11 requests and HID 1.11 boot protocol (appendix B), US
keyboard layout (HID usage tables, keyboard page 0x07).
-/
namespace LeanOS.Usb.Keyboard

open LeanOS.Wifi.Bytecode LeanOS.Usb.Xhci LeanOS.Usb.Hid

variable [Layout]

namespace Tag
def leds : UInt32 := 0x2017
def key : UInt32 := 0x2100
def ready : UInt32 := 0x2101
def sessionEnd : UInt32 := 0x2102
def reports : UInt32 := 0x2103
/-- Diagnostic: a non-empty raw report (first and second dwords). -/
def rawReport : UInt32 := 0x2104
end Tag

namespace Fail
def noKeyboard : UInt32 := 0x7F20
def noBootInterface : UInt32 := 0x7F21
end Fail

/-- US layout: HID usage → ASCII, unshifted and shifted (usages 0..63). -/
def asciiTable (shifted : Bool) : Array UInt32 := Id.run do
  let mut t := Array.replicate 64 (0 : UInt32)
  for i in [0:26] do
    t := t.set! (4 + i) ((if shifted then 'A' else 'a').toNat + i).toUInt32
  let digits := if shifted then "!@#$%^&*()" else "1234567890"
  for i in [0:10] do
    t := t.set! (0x1E + i) (digits.toList.getD i ' ').toNat.toUInt32
  t := t.set! 0x28 0x0A          -- Enter
  t := t.set! 0x29 0x1B          -- Escape
  t := t.set! 0x2A 0x08          -- Backspace
  t := t.set! 0x2B 0x09          -- Tab
  t := t.set! 0x2C 0x20          -- Space
  let punct := if shifted then "_+{}|~:\"~<>?" else "-=[]\\#;'`,./"
  for i in [0:12] do
    t := t.set! (0x2D + i) (punct.toList.getD i ' ').toNat.toUInt32
  return t

def tableBytes : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for v in asciiTable false ++ asciiTable true do b := putU32 b v
  return b

/-! ## Keyboard setup and session -/

/-- The boot interface (SET_CONFIGURATION, interrupt IN endpoint,
SET_PROTOCOL(boot), SET_IDLE(`idle`)), then an LED sweep. -/
def setupKeyboard (idle : UInt32 := 0) : ProgM Unit := do
  setupInterface idle
  -- LED sweep: Num, Caps, Scroll, all, off (SET_REPORT output, 1 byte)
  for leds in ([1, 2, 4, 7, 0] : List UInt32) do
    st 1 dataBuf (.imm leds)
    ld 4 1 V.iface
    ori 1 ((1 : UInt32) <<< 16)
    control 1 V.hidSlot (.imm ((0x21 : UInt32) ||| ((0x09 : UInt32) <<< 8) ||| ((0x0200 : UInt32) <<< 16))) (.reg 1) 1 false
    printImm Tag.leds leds
    delay 250000

/-- Report `reportBuf` against `prevReport`: every newly pressed usage in
bytes 2–7 becomes one character (tag 0x2100), counted in `V.records`. -/
def decodeReport (tableOff : UInt32) (yieldKeys : Bool := false) : ProgM Unit := do
  ld 1 8 reportBuf                              -- modifiers
  andi 8 0x22                                   -- either Shift
  for i in [2:8] do
    let skip ← newLabel
    ld 1 1 (reportBuf + i.toUInt32)
    emit (.branch .ltu 1 (.imm 4) skip)
    emit (.branch .geu 1 (.imm 64) skip)
    for j in [2:8] do
      ld 1 2 (prevReport + j.toUInt32)
      emit (.branch .eq 1 (.reg 2) skip)
    mov 3 1
    let noShift ← newLabel
    emit (.branch .eq 8 (.imm 0) noShift)
    addi 3 64
    place noShift
    emit (.blobLoad32 4 3 tableOff)
    emit (.branch .eq 4 (.imm 0) skip)
    -- Hand the key to the invoking subject (device service), or print it.
    if yieldKeys then emit (.yield (.reg 4)) else print Tag.key 4
    ld 4 5 V.records
    addi 5 1
    st 4 V.records (.reg 5)
    place skip
  for i in [0:8] do
    ld 1 1 (reportBuf + i.toUInt32)
    st 1 (prevReport + i.toUInt32) (.reg 1)

/-- Echo keys for `seconds` of controller time (MFINDEX, 125 µs units). -/
def session (seconds : UInt32) (tableOff : UInt32) (yieldKeys : Bool := false)
    (trace : Bool := false) : ProgM Unit :=
  Hid.session seconds { ready := Tag.ready, reports := Tag.reports, sessionEnd := Tag.sessionEnd } do
    if trace then
      let quiet ← newLabel
      ld 4 1 reportBuf
      ld 4 2 (reportBuf + 4)
      mov 3 1
      emit (.alu .or 3 (.reg 2))
      emit (.branch .eq 3 (.imm 0) quiet)
      print Tag.rawReport 1
      print Tag.rawReport 2
      place quiet
    decodeReport tableOff yieldKeys

/-- The complete keyboard program: controller bring-up, enumeration through
at most one hub or directly on a root port, keyboard setup, and a `seconds`-long echo session. With
`yieldKeys` each typed character is handed to the invoking subject by
`yield` (the device-service form, ADR 0022) instead of being printed. -/
def program (seconds : UInt32) (idle : UInt32 := 0) (yieldKeys : Bool := false)
    (trace : Bool := false) : ProgM Unit := do
  let tableOff ← addBlob "hid-us-ascii" tableBytes
  attach Protocol.keyboard Fail.noKeyboard
  setupKeyboard idle
  session seconds tableOff yieldKeys trace
  halt

end LeanOS.Usb.Keyboard
