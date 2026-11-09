import LeanOS.Usb.Mouse
import LeanOS.Wifi.Sim

/-! Simulated check of the USB mouse report decoder: synthetic HID boot mouse
reports (buttons, dx, dy and an optional wheel byte, with the transfer
event's residual) go through `decodeReport`, and the emitted records are
compared with the expected motion and button changes. -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi LeanOS.Usb.Xhci LeanOS.Usb.Hid LeanOS.Usb.Mouse

attribute [local instance] LeanOS.Usb.Xhci.qemu

/-- A report as received from an endpoint with max packet size 4: its bytes
(the residual is 4 − length). -/
def reports : List (List UInt8) :=
  [ [0, 10, 5, 0],          -- move
    [0, 0, 0, 0],           -- no motion, no change: dropped
    [1, 0, 0, 0],           -- left pressed
    [1, 0xF6, 0x81, 0],     -- drag by (−10, −127)
    [1, 0, 0, 0],           -- held, no motion: dropped
    [0, 0, 0, 0],           -- released
    [0, 0, 0, 0xFF],        -- wheel −1
    [0x06, 0x7F, 0, 1],     -- right and middle pressed, dx 127, wheel +1
    [0x06, 0, 0x02],        -- 3-byte report: no wheel byte, dy 2
    [0x06, 0, 0],           -- 3-byte report, no change: dropped
    [0x06, 3],              -- 2 bytes: not a boot report, dropped
    [0, 0, 0] ]             -- released (3 bytes)

def expected : List Record :=
  [ ⟨0, 10, 5, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, -10, -127, 0⟩, ⟨0, 0, 0, 0⟩,
    ⟨0, 0, 0, -1⟩, ⟨6, 127, 0, 1⟩, ⟨6, 0, 2, 0⟩, ⟨0, 0, 0, 0⟩ ]

def prog : ProgM Unit := do
  st 4 V.records (.imm 0)
  st 4 V.epMps (.imm 4)
  for r in reports do
    -- The controller writes only the bytes it received: stale bytes stay.
    for h : i in [0:r.length] do
      st 1 (reportBuf + i.toUInt32) (.imm r[i].toUInt32)
    -- Transfer event dword 2: completion code | residual.
    let residual := 4 - r.length.toUInt32
    st 4 Var.ev2 (.imm ((if residual == 0 then (1 : UInt32) else 13) <<< 24 ||| residual))
    decodeReport
  ld 4 1 V.records
  print 0x2FFF 1                                -- records counted
  halt

def main : IO UInt32 := do
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let (st, m) := Sim.run p Sim.Device.none ()
    let got := m.prints.toList.filter (·.1 == Tag.motion) |>.map (Record.ofWord ·.2)
    let count := m.prints.toList.filter (·.1 == 0x2FFF) |>.map (·.2)
    IO.println s!"status {repr st} records {got.length}: {repr got}"
    let ok := st == .halt && got == expected && count == [expected.length.toUInt32]
    IO.println (if ok then "PASS usb mouse report decoding" else s!"FAIL expected {repr expected}")
    return if ok then 0 else 1
