import LeanOS.Usb.Keyboard
import LeanOS.Wifi.Sim

/-! Simulated check of the USB keyboard report decoder: synthetic HID boot
reports (modifiers, reserved, six usages) go through `decodeReport` and the
emitted characters are compared with the expected text. -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi LeanOS.Usb.Keyboard LeanOS.Usb.Xhci LeanOS.Usb.Hid

attribute [local instance] LeanOS.Usb.Xhci.qemu

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
  st 4 V.records (.imm 0)
  for r in reports do
    for h : i in [0:r.length] do
      st 1 (reportBuf + i.toUInt32) (.imm r[i].toUInt32)
    decodeReport tableOff
  halt

/-- Lock keys: Caps Lock inverts Shift for letters only, Num Lock and a second
Caps Lock press toggle their bits, and a held lock key toggles once. -/
def capsLock : UInt8 := 0x39
def numLock : UInt8 := 0x53

def lockReports : List (List UInt8) :=
  [ rep 0 [0x04], rep 0 [],                                       -- a
    rep 0 [capsLock], rep 0 [capsLock], rep 0 [],                 -- Caps on (held)
    rep 0 [0x05], rep 0 [],                                       -- B
    rep shift [0x06], rep 0 [],                                   -- c (Shift inverted)
    rep 0 [0x1E], rep 0 [], rep shift [0x1E], rep 0 [],           -- 1 then ! (digits: Shift only)
    rep 0 [numLock], rep 0 [],                                    -- Num on
    rep 0 [capsLock], rep 0 [],                                   -- Caps off
    rep 0 [0x07], rep 0 [] ]                                      -- d

def lockExpected : List UInt32 := "aBc1!d".toList.map (·.toNat.toUInt32)
/-- The lock state after each change: Caps, Caps | Num, Num. -/
def lockStates : List UInt32 := [2, 3, 1]

def lockProg : ProgM Unit := do
  let tableOff ← addBlob "hid-us-ascii" tableBytes
  st 4 V.records (.imm 0)
  st 4 K.locks (.imm 0)
  for r in lockReports do
    for h : i in [0:r.length] do
      st 1 (reportBuf + i.toUInt32) (.imm r[i].toUInt32)
    decodeReport tableOff
  halt

def check (name : String) (p : ProgM Unit) (keys : List UInt32) (locks : List UInt32) :
    IO Bool := do
  match build p with
  | .error e => IO.eprintln e; return false
  | .ok p =>
    let (st, m) := Sim.run p Sim.Device.none ()
    let got := m.prints.toList.filter (·.1 == Tag.key) |>.map (·.2)
    let gotLocks := m.prints.toList.filter (·.1 == Tag.locks) |>.map (·.2)
    let text := String.ofList (got.map fun c => Char.ofNat c.toNat)
    IO.println s!"{name}: status {repr st} keys {got.length}: {repr text} locks {gotLocks}"
    return st == .halt && got == keys && gotLocks == locks

def main : IO UInt32 := do
  let plain ← check "decode" prog expected []
  let locks ← check "locks" lockProg lockExpected lockStates
  let ok := plain && locks
  IO.println (if ok then "PASS usb keyboard report decoding, lock keys"
    else s!"FAIL expected {repr expected} and {repr lockExpected} with locks {lockStates}")
  return if ok then 0 else 1
