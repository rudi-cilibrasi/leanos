import LeanOS.Usb.MassStorage
import LeanOS.Wifi.Sim

/-! Simulated check of the USB mass-storage program's data handling: two
blocks of known bytes in the data buffer go through `reportBlocks`, whose
records (LBA, first 16 bytes, FNV-1a of the block) are compared with the
same values computed here, and a READ CAPACITY(10) reply's big-endian words
go through `ldBe32`. -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi LeanOS.Usb.Xhci LeanOS.Usb.MassStorage

attribute [local instance] LeanOS.Usb.Xhci.qemu

def blockLen : Nat := 512
def firstLba : Nat := 8190

/-- Byte `i` of block `lba`: depends on both, so a swapped block or a shifted
offset changes the hash. -/
def byteOf (lba i : Nat) : UInt8 := ((lba * 131 + i * 7 + i / 256 * 3) % 256).toUInt8

def blockData (lba : Nat) : List UInt8 := (List.range blockLen).map (byteOf lba)

/-- 32-bit FNV-1a. -/
def fnv1a (bytes : List UInt8) : UInt32 :=
  bytes.foldl (fun h b => (h ^^^ b.toUInt32) * 0x01000193) 0x811C9DC5

/-- Little-endian dword `j` of `bytes`. -/
def dword (bytes : List UInt8) (j : Nat) : UInt32 :=
  (List.range 4).foldl (fun acc i => acc ||| ((bytes.getD (4 * j + i) 0).toUInt32 <<< (8 * i).toUInt32)) 0

def capacityReply : List UInt8 := [0x00, 0x00, 0x1F, 0xFF, 0x00, 0x00, 0x02, 0x00]

def expected : List (UInt32 × UInt32) :=
  ((List.range 2).flatMap fun k =>
    let d := blockData (firstLba + k)
    [(Tag.block, (firstLba + k).toUInt32)] ++ (List.range 4).map (fun j => (Tag.head, dword d j)) ++
      [(Tag.fnv, fnv1a d)]) ++
  [(0x2FFF, 2), (0x2FFE, 0x1FFF), (0x2FFE, 0x200)]

def prog : ProgM Unit := do
  st 4 M.blockBytes (.imm blockLen.toUInt32)
  st 4 M.lba (.imm firstLba.toUInt32)
  st 4 M.blocksRead (.imm 0)
  for k in [0:2] do
    for i in [0:blockLen] do
      st 1 (xferBuf + (k * blockLen + i).toUInt32) (.imm (byteOf (firstLba + k) i).toUInt32)
  reportBlocks 2
  ld 4 1 M.blocksRead
  print 0x2FFF 1                                -- blocks counted
  for h : i in [0:capacityReply.length] do
    st 1 (xferBuf + i.toUInt32) (.imm capacityReply[i].toUInt32)
  ldBe32 1 2 xferBuf
  print 0x2FFE 1                                -- last LBA
  ldBe32 1 2 (xferBuf + 4)
  print 0x2FFE 1                                -- block length
  halt

def main : IO UInt32 := do
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let (st, m) := Sim.run p Sim.Device.none ()
    let got := m.prints.toList
    IO.println s!"status {repr st}, {got.length} records"
    let ok := st == .halt && got == expected
    IO.println (if ok then "PASS usb mass-storage block report and capacity parsing"
                else s!"FAIL got {repr got}, expected {repr expected}")
    return if ok then 0 else 1
