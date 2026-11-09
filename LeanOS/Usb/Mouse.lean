import LeanOS.Usb.Hid

/-
USB mouse for LeanOS: find a boot-protocol HID mouse (interface class 3,
subclass 1, protocol 2; directly on a root port or behind one USB 2.0 hub),
configure it for the boot protocol and turn its reports into motion and
button records for a bounded session. Controller, hub handling, enumeration
and the session loop are the keyboard's (`LeanOS/Usb/Hid.lean`).

HID 1.11 appendix B.2, boot mouse report: byte 0 the buttons (bits 0–2 are
buttons 1–3, the others device-specific), bytes 1 and 2 the X and Y
displacement as signed bytes. A device may append bytes; most mice, QEMU's
`usb-mouse` among them, send the wheel as a signed byte 3.
-/
namespace LeanOS.Usb.Mouse

open LeanOS.Wifi.Bytecode LeanOS.Usb.Xhci LeanOS.Usb.Hid

variable [Layout]

namespace Tag
/-- One report that moves or changes the buttons: buttons | dx << 8 |
dy << 16 | wheel << 24, each motion field a two's-complement byte. -/
def motion : UInt32 := 0x2200
def ready : UInt32 := 0x2201
def sessionEnd : UInt32 := 0x2202
def reports : UInt32 := 0x2203
end Tag

namespace Fail
def noMouse : UInt32 := 0x7F22
end Fail

/-- The record word of a packed report: buttons | dx << 8 | dy << 16 |
wheel << 24 (the hosted reading of `Tag.motion`). -/
structure Record where
  buttons : Nat
  dx : Int
  dy : Int
  wheel : Int
  deriving BEq, Repr

/-- Read a `Tag.motion` value back into its fields. -/
def Record.ofWord (w : UInt32) : Record :=
  let s (b : UInt32) : Int := let v := (b &&& 0xFF).toNat; if v ≥ 128 then v - 256 else v
  { buttons := (w &&& 0xFF).toNat, dx := s (w >>> 8), dy := s (w >>> 16), wheel := s (w >>> 24) }

/-- Decode the report in `reportBuf`. Its length is the endpoint's max packet
size less the residual of the transfer event (`Var.ev2` bits 0–23); a report
of fewer than 3 bytes is not a boot report and is dropped, and the wheel is
byte 3 when the report has one (else 0). A report that neither moves (dx, dy,
wheel all 0) nor changes the buttons (against `prevReport` byte 0) is
dropped too; any other becomes one `Tag.motion` record. -/
def decodeReport : ProgM Unit := do
  -- bytes received = max packet size − residual
  ld 4 1 Var.ev2
  andi 1 0xFFFFFF
  ld 4 2 V.epMps
  emit (.alu .sub 2 (.reg 1))
  let skip ← newLabel
  emit (.branch .ltu 2 (.imm 3) skip)
  ld 4 3 reportBuf
  andi 3 0xFFFFFF                               -- buttons, dx, dy
  let short ← newLabel
  emit (.branch .ltu 2 (.imm 4) short)
  ld 1 4 (reportBuf + 3)                        -- wheel
  shli 4 24
  emit (.alu .or 3 (.reg 4))
  place short
  let record ← newLabel
  mov 4 3
  andi 4 0xFFFFFF00
  emit (.branch .ne 4 (.imm 0) record)          -- it moves
  mov 4 3
  andi 4 0xFF
  ld 1 5 prevReport
  emit (.branch .eq 4 (.reg 5) skip)            -- same buttons, no motion
  place record
  print Tag.motion 3
  ld 4 5 V.records
  addi 5 1
  st 4 V.records (.reg 5)
  andi 3 0xFF
  st 1 prevReport (.reg 3)
  place skip

/-- The complete mouse program: controller bring-up, enumeration through at
most one hub or directly on a root port, boot protocol with no idle repeat
(HID 1.11 §7.2.4 recommends 0 for mice), and a `seconds`-long session of
motion and button records. -/
def program (seconds : UInt32) : ProgM Unit := do
  attach Protocol.mouse Fail.noMouse
  setupInterface 0
  st 1 prevReport (.imm 0)                      -- no button pressed
  session seconds { ready := Tag.ready, reports := Tag.reports, sessionEnd := Tag.sessionEnd }
    decodeReport
  halt

end LeanOS.Usb.Mouse
