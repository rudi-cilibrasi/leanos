import LeanOS.Wifi.DevCrypto
import LeanOS.Wifi.Sim
import LeanOS.Wifi.Eapol

/-! Emit a computation-only program (PTK derivation and a message-2 MIC on
fixed inputs, results printed as words) for the C host runner, and print the
simulator's transcript of the same program for comparison.

usage: leanos-wifi-xcheck <out.bin> -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi.DevCrypto LeanOS.Wifi

def bytesOf (n : Nat) (seed : Nat) : ByteArray :=
  ByteArray.mk ((List.range n).map (fun i => ((i * 37 + seed * 101 + 11) % 256).toUInt8)).toArray

def store (at_ : UInt32) (b : ByteArray) : ProgM Unit := do
  li 1 at_
  for h : i in [0:b.size] do
    emit (.memStore 1 1 i.toUInt32 (.imm b[i].toUInt32))

def prog : ProgM Unit := do
  let L ← install
  store 0x100 (bytesOf 32 1)   -- PMK
  store 0x140 (bytesOf 6 2)    -- AA
  store 0x150 (bytesOf 6 3)    -- SPA
  store 0x160 (bytesOf 32 4)   -- ANonce
  store 0x1a0 (bytesOf 32 5)   -- SNonce
  callPtk L (.imm 0x100) (.imm 0x140) (.imm 0x150) (.imm 0x160) (.imm 0x1a0) (.imm 0x200)
  for k in [0:12] do
    li 1 0
    emit (.memLoad 4 2 1 (0x200 + 4 * k.toUInt32))
    print (0x100 + k.toUInt32) 2
  store 0x300 (bytesOf 121 6)
  callMicCompute L (.imm 0x200) (.imm 0x300) (.imm 121)
  for k in [0:4] do
    li 1 0
    emit (.memLoad 4 2 1 (0x300 + 81 + 4 * k.toUInt32))
    print (0x200 + k.toUInt32) 2
  halt

def main (args : List String) : IO UInt32 := do
  let some out := args.head? | return 2
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    IO.FS.writeBinFile out p.image
    let (st, m) := Sim.run p Sim.Device.none ()
    for (t, v) in m.prints do
      IO.println s!"WIFI {String.ofList (Nat.toDigits 16 t.toNat)} {v}"
    IO.println s!"SIM-END {repr st}"
    return 0
