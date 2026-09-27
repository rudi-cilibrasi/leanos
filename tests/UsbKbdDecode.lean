import LeanOS.Usb.Keyboard
import LeanOS.Wifi.Sim

/-! Simulated check of the USB keyboard report decoder: synthetic HID boot
reports (modifiers, reserved, six usages) go through `decodeReport` and the
emitted characters are compared with the expected text. -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi LeanOS.Usb.Keyboard LeanOS.Usb.Xhci

/-- A report: modifier byte and up to six pressed usages. -/
def rep (mods : UInt8) (keys : List UInt8) : List UInt8 :=
  [mods, 0] ++ (keys ++ List.replicate 6 0).take 6

def shift : UInt8 := 0x02

/-- "Hello, World!" then Enter, Backspace; with a held key (no repeat) and a
two-key rollover. -/
def reports : List (List UInt8) :=
  [ rep shift [0x0B], rep 0 [], rep 0 [0x08], rep 0 [],          -- H e
    rep 0 [0x0F], rep 0 [0x0F], rep 0 [], rep 0 [0x0F], rep 0 [],  -- l (held) l
    rep 0 [0x12], rep 0 [0x36], rep 0 [], rep 0 [0x2C], rep 0 [],  -- o , space
    rep shift [0x1A], rep 0 [0x1A, 0x12], rep 0 [0x12], rep 0 [], -- W, then o while w held
    rep 0 [0x15], rep 0 [0x0F], rep 0 [0x07], rep 0 [],           -- r l d
    rep shift [0x1E], rep 0 [], rep 0 [0x28], rep 0 [0x2A], rep 0 [] ] -- ! Enter BS

def expected : List UInt32 :=
  ("Hello, World!".toList.map (·.toNat.toUInt32)) ++ [0x0A, 0x08]

def prog : ProgM Unit := do
  let tableOff ← addBlob "hid-us-ascii" tableBytes
  st 4 V.keys (.imm 0)
  for r in reports do
    for h : i in [0:r.length] do
      st 1 (reportBuf + i.toUInt32) (.imm r[i].toUInt32)
    decodeReport tableOff
  halt

def main : IO UInt32 := do
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let (st, m) := Sim.run p Sim.Device.none ()
    let got := m.prints.toList.filter (·.1 == Tag.key) |>.map (·.2)
    let text := String.ofList (got.map fun c => Char.ofNat c.toNat)
    IO.println s!"status {repr st} keys {got.length}: {repr text}"
    let ok := st == .halt && got == expected
    IO.println (if ok then "PASS usb keyboard report decoding" else s!"FAIL expected {repr expected}")
    return if ok then 0 else 1
