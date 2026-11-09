import LeanOS.Usb.MassStorage

/-
Read one file from a FAT32 volume on a USB mass-storage device: the MBR's
first FAT32 partition, its boot sector (BPB), the 8.3 short-name path through
the directories, then the file's cluster chain, hashed with FNV-1a.

Built on the bulk-only-transport reader (`LeanOS/Usb/MassStorage.lean`): the
same enumeration, endpoints, INQUIRY, TEST UNIT READY and READ CAPACITY(10),
then READ(10) of one 512-byte block at a time into `xferBuf`.

Microsoft FAT32 File System Specification 1.03 (BPB fields, the FAT entry's
low 28 bits, end of chain ≥ 0x0FFFFFF8, directory entries of 32 bytes: name
0–10, attributes 11, first cluster high 20–21 and low 26–27, size 28–31);
the MBR partition table at 446 (four 16-byte entries: status 0, type 4,
first LBA 8–11, blocks 12–15) and signature 0x55 0xAA at 510.

Every loop is bounded and every cluster number is checked against the
volume before it is used, so a corrupt volume stops the program with an
`MSC error=` record instead of reading outside the volume or looping.
-/
namespace LeanOS.Usb.Fat32

open LeanOS.Wifi.Bytecode LeanOS.Usb.Xhci LeanOS.Usb.Hid LeanOS.Usb.MassStorage

variable [Layout]

/- Steps of the file reader (continuing `MassStorage.Step`). -/
namespace FStep
def mbr : UInt32 := 8
def volume : UInt32 := 9
def lookup : UInt32 := 10
def file : UInt32 := 11
end FStep

/- Why the file reader stops (continuing `MassStorage.Reason`). -/
namespace FReason
/-- No MBR signature, or no partition of type 0x0B or 0x0C. -/
def noPartition : UInt32 := 15
/-- The partition's boot sector is not a FAT32 BPB this reader handles (detail:
the field that failed). -/
def notFat32 : UInt32 := 16
/-- A path component is not in its directory (detail: the component). -/
def notFound : UInt32 := 17
/-- A cluster number outside the volume, in a directory entry or the FAT
(detail: the number). -/
def badCluster : UInt32 := 18
/-- A path component before the last is not a directory, or the last one is
(detail: the component). -/
def wrongKind : UInt32 := 19
/-- A cluster chain longer than `maxChain` (detail: the cluster). -/
def chainTooLong : UInt32 := 20
/-- The file's cluster chain ended before its size (detail: bytes left). -/
def chainShort : UInt32 := 21
end FReason

namespace FTag
/-- An MBR partition entry: index | type << 8 | active << 16 (line continues),
its first LBA (continues), its blocks (line ends). -/
def partition : UInt32 := 0x2360
def partitionLba : UInt32 := 0x2361
def partitionBlocks : UInt32 := 0x2362
/-- The FAT32 BPB: sectors per cluster | FATs << 8 (line continues), the
reserved sectors, the sectors per FAT, then the root cluster (line ends). -/
def volume : UInt32 := 0x2370
def volumeReserved : UInt32 := 0x2371
def volumeFatBlocks : UInt32 := 0x2372
def volumeRoot : UInt32 := 0x2373
/-- A path component found: component index | attributes << 8 (line
continues), its first cluster (continues), its size in bytes (line ends). -/
def entry : UInt32 := 0x2380
def entryCluster : UInt32 := 0x2381
def entryBytes : UInt32 := 0x2382
/-- The file: its size (line continues), its first 16 bytes as four
little-endian dwords (continues), the FNV-1a hash of its bytes (continues),
then the clusters read (line ends). -/
def file : UInt32 := 0x2390
def fileHead : UInt32 := 0x2391
def fileFnv : UInt32 := 0x2392
def fileClusters : UInt32 := 0x2393
end FTag

/- The reader's scratch words (after `MassStorage.M`'s). -/
namespace F
def partStart : UInt32 := vars + 0x260
def spc : UInt32 := vars + 0x264
def fatStart : UInt32 := vars + 0x268
def dataStart : UInt32 := vars + 0x26C
/-- The current directory's or file's cluster. -/
def cluster : UInt32 := vars + 0x270
/-- One past the volume's last cluster number. -/
def clusterLimit : UInt32 := vars + 0x274
def size : UInt32 := vars + 0x278
def left : UInt32 := vars + 0x27C
def hash : UInt32 := vars + 0x280
def sector : UInt32 := vars + 0x284
def steps : UInt32 := vars + 0x288
def attr : UInt32 := vars + 0x28C
def clustersRead : UInt32 := vars + 0x290
def head : UInt32 := vars + 0x294             -- 16 bytes
/-- The step the block-read subroutine reports (`readOne`). -/
def readStep : UInt32 := vars + 0x2A4
end F

/-- Bytes per block (and per sector) this reader handles. -/
def sectorBytes : UInt32 := 512
/-- FAT entries per FAT sector (4 bytes each). -/
def entriesPerFatSector : UInt32 := sectorBytes / 4
/-- Clusters followed in one chain at most: 1 GiB of 512-byte clusters is far
beyond any file or directory this reader is for. -/
def maxChain : UInt32 := 0x200000
/-- End-of-chain marks are 0x0FFFFFF8 and above (FAT entries keep 28 bits). -/
def endOfChain : UInt32 := 0x0FFFFFF8
/-- The directory-entry attribute bits used here. -/
def attrDirectory : UInt32 := 0x10
def attrVolume : UInt32 := 0x08
def attrLongName : UInt32 := 0x0F

/-- An 8.3 short name in its directory-entry form: the base name upper-cased
and padded to 8 bytes with spaces, then the extension to 3. `none` when the
component does not fit 8.3 (the reader matches short names only). -/
def shortName (component : String) : Option (Array UInt8) :=
  let up := component.toUpper
  let (base, ext) := match up.splitOn "." with
    | [b] => (b, "")
    | [b, e] => (b, e)
    | _ => ("", "")
  let ok (s : String) (n : Nat) := 0 < s.length || n == 3
  if base.length == 0 || base.length > 8 || ext.length > 3 || !ok base 8 ||
      up.any (fun c => c == ' ' || c.toNat > 0x7E || c.toNat < 0x21) then none
  else
    let pad (s : String) (n : Nat) : List UInt8 :=
      (s.toList.map (·.toNat.toUInt8)) ++ List.replicate (n - s.length) 0x20
    some (pad base 8 ++ pad ext 3).toArray

/-- `dst` := the little-endian value of bytes `i ..< i + w` of `name`. -/
def nameWord (name : Array UInt8) (i w : Nat) : UInt32 := Id.run do
  let mut v : UInt32 := 0
  for k in [0:w] do
    v := v ||| ((name.getD (i + k) 0).toUInt32 <<< (8 * k).toUInt32)
  return v

/-- The block-read subroutine at `entry`, placed once: READ(10) of the one
block at `M.lba` into `xferBuf`, which must pass and move all 512 bytes, the
step in `F.readStep` naming it in the records. One BOT command expands to
hundreds of instructions (with its stall recovery), so the reader calls this
instead of inlining it at each of its ten reads. -/
def readSubroutine (err : Nat) (entry : Nat) : ProgM Unit := do
  place entry
  ld 4 8 F.readStep
  read10 err (.reg 8) 1
  passed err
  ld 4 1 M.residual
  let whole ← newLabel
  emit (.branch .eq 1 (.imm 0) whole)
  stop err MassStorage.Stage.data MassStorage.Reason.shortRead (.reg 1)
  place whole
  emit .ret

/-- Read the block at `M.lba` for `step` through the subroutine at `rd`. -/
def readOne (rd : Nat) (step : UInt32) : ProgM Unit := do
  st 4 F.readStep (.imm step)
  emit (.call rd)

/-- Stop through `err` unless 2 ≤ r1 < `F.clusterLimit` (uses r2). -/
def checkCluster (err : Nat) (stage : UInt32) : ProgM Unit := do
  let bad ← newLabel
  let ok ← newLabel
  emit (.branch .ltu 1 (.imm 2) bad)
  ld 4 2 F.clusterLimit
  emit (.branch .ltu 1 (.reg 2) ok)
  place bad
  stop err stage FReason.badCluster (.reg 1)
  place ok

/-- `M.lba` := the first block of cluster `F.cluster` plus `F.sector`:
dataStart + (cluster − 2) × spc + sector. -/
def sectorLba : ProgM Unit := do
  ld 4 1 F.cluster
  emit (.alu .sub 1 (.imm 2))
  ld 4 2 F.spc
  emit (.alu .mul 1 (.reg 2))
  ld 4 2 F.dataStart
  emit (.alu .add 1 (.reg 2))
  ld 4 2 F.sector
  emit (.alu .add 1 (.reg 2))
  st 4 M.lba (.reg 1)

/-- Follow the FAT from `F.cluster`: read the FAT sector that holds its entry
and either jump to `done` (end of chain) or store the next cluster, which
must lie in the volume, and count the step (at most `maxChain`). -/
def nextCluster (err rd : Nat) (step : UInt32) (done : Nat) : ProgM Unit := do
  ld 4 1 F.cluster
  shri 1 7                                       -- / entriesPerFatSector
  ld 4 2 F.fatStart
  emit (.alu .add 1 (.reg 2))
  st 4 M.lba (.reg 1)
  readOne rd step
  ld 4 3 F.cluster
  andi 3 (entriesPerFatSector - 1)
  shli 3 2
  emit (.memLoad 4 1 3 xferBuf)
  andi 1 0x0FFFFFFF
  emit (.branch .geu 1 (.imm endOfChain) done)
  checkCluster err MassStorage.Stage.data
  st 4 F.cluster (.reg 1)
  ld 4 2 F.steps
  addi 2 1
  st 4 F.steps (.reg 2)
  let more ← newLabel
  emit (.branch .ltu 2 (.imm maxChain) more)
  stop err MassStorage.Stage.data FReason.chainTooLong (.reg 1)
  place more

/-- The MBR at LBA 0: its signature, a record per used entry, and
`F.partStart` := the first LBA of the first FAT32 partition (type 0x0B or
0x0C). -/
def readMbr (err rd : Nat) : ProgM Unit := do
  st 4 M.lba (.imm 0)
  readOne rd FStep.mbr
  ld 2 1 (xferBuf + 510)
  let signed ← newLabel
  emit (.branch .eq 1 (.imm 0xAA55) signed)
  stop err MassStorage.Stage.data FReason.noPartition (.reg 1)
  place signed
  st 4 F.partStart (.imm 0)
  for i in [0:4] do
    let e := xferBuf + 446 + 16 * i.toUInt32
    let unused ← newLabel
    ld 1 2 (e + 4)                               -- type
    emit (.branch .eq 2 (.imm 0) unused)
    ld 1 3 e                                     -- status: 0x80 active
    shri 3 7
    shli 3 16
    mov 1 2
    shli 1 8
    emit (.alu .or 1 (.reg 3))
    ori 1 i.toUInt32
    print FTag.partition 1
    ld 4 1 (e + 8)
    print FTag.partitionLba 1
    ld 4 1 (e + 12)
    print FTag.partitionBlocks 1
    ld 4 4 F.partStart
    emit (.branch .ne 4 (.imm 0) unused)         -- the first FAT32 one wins
    let fat32 ← newLabel
    emit (.branch .eq 2 (.imm 0x0B) fat32)
    emit (.branch .ne 2 (.imm 0x0C) unused)
    place fat32
    ld 4 1 (e + 8)
    st 4 F.partStart (.reg 1)
    place unused
  ld 4 1 F.partStart
  let found ← newLabel
  emit (.branch .ne 1 (.imm 0) found)
  stop err MassStorage.Stage.data FReason.noPartition (.imm 0)
  place found

/-- The partition's boot sector: a FAT32 BPB with 512-byte sectors (the
device's block length too), a power-of-two cluster size, one or two FATs
and the root directory's cluster in the volume; sets the reader's geometry
and prints it. -/
def readVolume (err rd : Nat) : ProgM Unit := do
  ld 4 1 F.partStart
  st 4 M.lba (.reg 1)
  readOne rd FStep.volume
  let fail (field : UInt32) : ProgM Unit := stop err MassStorage.Stage.data FReason.notFat32 (.imm field)
  let check (cond : Cond) (r : Reg) (v : Operand) (field : UInt32) : ProgM Unit := do
    let ok ← newLabel
    emit (.branch cond r v ok)
    fail field
    place ok
  ld 2 1 (xferBuf + 510)
  check .eq 1 (.imm 0xAA55) 510
  ld 4 1 M.blockBytes
  check .eq 1 (.imm sectorBytes) 0
  ld 2 1 (xferBuf + 11)                          -- BPB_BytsPerSec
  check .eq 1 (.imm sectorBytes) 11
  ld 1 1 (xferBuf + 13)                          -- BPB_SecPerClus
  check .ne 1 (.imm 0) 13
  mov 2 1
  emit (.alu .sub 2 (.imm 1))
  emit (.alu .and 2 (.reg 1))
  check .eq 2 (.imm 0) 13                        -- a power of two
  st 4 F.spc (.reg 1)
  ld 2 1 (xferBuf + 14)                          -- BPB_RsvdSecCnt
  check .ne 1 (.imm 0) 14
  ld 4 2 F.partStart
  emit (.alu .add 1 (.reg 2))
  st 4 F.fatStart (.reg 1)
  ld 1 1 (xferBuf + 16)                          -- BPB_NumFATs
  check .ne 1 (.imm 0) 16
  check .ltu 1 (.imm 3) 16
  ld 2 1 (xferBuf + 22)                          -- BPB_FATSz16: 0 on FAT32
  check .eq 1 (.imm 0) 22
  ld 4 2 (xferBuf + 36)                          -- BPB_FATSz32
  check .ne 2 (.imm 0) 36
  ld 1 1 (xferBuf + 16)
  emit (.alu .mul 1 (.reg 2))
  ld 4 3 F.fatStart
  emit (.alu .add 1 (.reg 3))
  st 4 F.dataStart (.reg 1)
  -- clusterLimit := (TotSec32 − (dataStart − partStart)) / spc + 2, and no more
  -- than the FAT can describe
  ld 4 3 F.partStart
  emit (.alu .sub 1 (.reg 3))                    -- blocks before the data
  ld 4 3 (xferBuf + 32)                          -- BPB_TotSec32
  check .ltu 1 (.reg 3) 32
  emit (.alu .sub 3 (.reg 1))
  ld 4 4 F.spc
  emit (.alu .udiv 3 (.reg 4))
  addi 3 2
  shli 2 7                                       -- FATSz32 × entries per sector
  let fits ← newLabel
  emit (.branch .ltu 3 (.reg 2) fits)
  mov 3 2
  place fits
  st 4 F.clusterLimit (.reg 3)
  ld 4 1 (xferBuf + 44)                          -- BPB_RootClus
  checkCluster err MassStorage.Stage.data
  st 4 F.cluster (.reg 1)
  ld 4 1 F.spc
  ld 1 2 (xferBuf + 16)
  shli 2 8
  emit (.alu .or 1 (.reg 2))
  print FTag.volume 1
  ld 2 1 (xferBuf + 14)
  print FTag.volumeReserved 1
  ld 4 1 (xferBuf + 36)
  print FTag.volumeFatBlocks 1
  ld 4 1 F.cluster
  print FTag.volumeRoot 1

/-- Find component `index` (short name `name`) in the directory whose first
cluster is `F.cluster`: scan its entries a block at a time along its chain,
past deleted, long-name and volume-label entries, until the name matches
(then `F.cluster`, `F.size` and `F.attr` are the entry's) or the
directory's end marker or chain end (`FReason.notFound`). The entry must be a
directory when `directory`, a file otherwise. -/
def lookup (err rd : Nat) (index : Nat) (name : Array UInt8) (directory : Bool) :
    ProgM Unit := do
  st 4 F.steps (.imm 0)
  let clusterTop ← newLabel
  let sectorTop ← newLabel
  let entryTop ← newLabel
  let next ← newLabel
  let missing ← newLabel
  let found ← newLabel
  place clusterTop
  st 4 F.sector (.imm 0)
  place sectorTop
  sectorLba
  readOne rd FStep.lookup
  li 3 0
  place entryTop
  emit (.memLoad 1 1 3 xferBuf)
  emit (.branch .eq 1 (.imm 0) missing)          -- end of the directory
  emit (.branch .eq 1 (.imm 0xE5) next)          -- deleted
  emit (.memLoad 1 2 3 (xferBuf + 11))
  emit (.branch .eq 2 (.imm attrLongName) next)
  andi 2 attrVolume
  emit (.branch .ne 2 (.imm 0) next)
  emit (.memLoad 4 4 3 xferBuf)
  emit (.branch .ne 4 (.imm (nameWord name 0 4)) next)
  emit (.memLoad 4 4 3 (xferBuf + 4))
  emit (.branch .ne 4 (.imm (nameWord name 4 4)) next)
  emit (.memLoad 2 4 3 (xferBuf + 8))
  emit (.branch .ne 4 (.imm (nameWord name 8 2)) next)
  emit (.memLoad 1 4 3 (xferBuf + 10))
  emit (.branch .ne 4 (.imm (nameWord name 10 1)) next)
  emit (.jump found)
  place next
  addi 3 32
  emit (.branch .ltu 3 (.imm sectorBytes) entryTop)
  ld 4 1 F.sector
  addi 1 1
  st 4 F.sector (.reg 1)
  ld 4 2 F.spc
  emit (.branch .ltu 1 (.reg 2) sectorTop)
  nextCluster err rd FStep.lookup missing
  emit (.jump clusterTop)
  place missing
  stop err MassStorage.Stage.data FReason.notFound (.imm index.toUInt32)
  place found
  emit (.memLoad 1 2 3 (xferBuf + 11))
  st 4 F.attr (.reg 2)
  emit (.memLoad 2 1 3 (xferBuf + 20))
  shli 1 16
  emit (.memLoad 2 4 3 (xferBuf + 26))
  emit (.alu .or 1 (.reg 4))
  emit (.memLoad 4 4 3 (xferBuf + 28))
  st 4 F.size (.reg 4)
  st 4 F.cluster (.reg 1)
  shli 2 8
  ori 2 index.toUInt32
  print FTag.entry 2
  print FTag.entryCluster 1
  print FTag.entryBytes 4
  ld 4 2 F.attr
  andi 2 attrDirectory
  let kindOk ← newLabel
  emit (.branch (if directory then .ne else .eq) 2 (.imm 0) kindOk)
  stop err MassStorage.Stage.data FReason.wrongKind (.imm index.toUInt32)
  place kindOk
  -- a file of 0 bytes has no cluster; anything else must start in the volume
  let empty ← newLabel
  if !directory then
    ld 4 4 F.size
    emit (.branch .eq 4 (.imm 0) empty)
  ld 4 1 F.cluster
  checkCluster err MassStorage.Stage.data
  place empty

/-- Read the file at `F.cluster` of `F.size` bytes along its chain, a block at
a time, hashing exactly its bytes (FNV-1a, as `reportBlocks`), and print its
size, first 16 bytes, hash and the clusters read. -/
def readFile (err rd : Nat) : ProgM Unit := do
  ld 4 1 F.size
  st 4 F.left (.reg 1)
  st 4 F.hash (.imm 0x811C9DC5)
  st 4 F.steps (.imm 0)
  st 4 F.clustersRead (.imm 0)
  for k in [0:4] do
    st 4 (F.head + 4 * k.toUInt32) (.imm 0)
  let clusterTop ← newLabel
  let sectorTop ← newLabel
  let hashTop ← newLabel
  let done ← newLabel
  let ended ← newLabel
  emit (.branch .eq 1 (.imm 0) done)
  place clusterTop
  ld 4 1 F.clustersRead
  addi 1 1
  st 4 F.clustersRead (.reg 1)
  st 4 F.sector (.imm 0)
  place sectorTop
  sectorLba
  readOne rd FStep.file
  -- the head: the first block's first 16 bytes
  ld 4 1 F.left
  ld 4 2 F.size
  let notFirst ← newLabel
  emit (.branch .ne 1 (.reg 2) notFirst)
  for k in [0:4] do
    ld 4 2 (xferBuf + 4 * k.toUInt32)
    st 4 (F.head + 4 * k.toUInt32) (.reg 2)
  place notFirst
  -- hash min(left, 512) bytes
  ld 4 4 F.left
  let whole ← newLabel
  emit (.branch .ltu 4 (.imm sectorBytes) whole)
  li 4 sectorBytes
  place whole
  ld 4 1 F.hash
  li 3 0
  place hashTop
  emit (.memLoad 1 2 3 xferBuf)
  emit (.alu .xor 1 (.reg 2))
  emit (.alu .mul 1 (.imm 0x01000193))
  addi 3 1
  emit (.branch .ltu 3 (.reg 4) hashTop)
  st 4 F.hash (.reg 1)
  ld 4 1 F.left
  emit (.alu .sub 1 (.reg 4))
  st 4 F.left (.reg 1)
  emit (.branch .eq 1 (.imm 0) done)
  ld 4 1 F.sector
  addi 1 1
  st 4 F.sector (.reg 1)
  ld 4 2 F.spc
  emit (.branch .ltu 1 (.reg 2) sectorTop)
  nextCluster err rd FStep.file ended
  emit (.jump clusterTop)
  place ended
  ld 4 1 F.left
  stop err MassStorage.Stage.data FReason.chainShort (.reg 1)
  place done
  ld 4 1 F.size
  print FTag.file 1
  for k in [0:4] do
    ld 4 1 (F.head + 4 * k.toUInt32)
    print FTag.fileHead 1
  ld 4 1 F.hash
  print FTag.fileFnv 1
  ld 4 1 F.clustersRead
  print FTag.fileClusters 1

/-- The complete file reader: the mass-storage program's enumeration,
endpoints, INQUIRY, TEST UNIT READY and READ CAPACITY(10), then the MBR, the
FAT32 volume, each component of `path` (8.3 short names; all but the last
are directories) and the file. The controller is stopped at the end; a
failed step stops it too, after its `MSC error=` record. `none` when a
component is not an 8.3 name or the path is empty. -/
def fileProgram (path : List String) : Option (ProgM Unit) := do
  let names ← path.mapM shortName
  guard (!names.isEmpty)
  some do
    let err ← newLabel
    let rd ← newLabel
    st 4 M.step (.imm MassStorage.Step.attach)
    attachWith bulkInterface (stop err MassStorage.Stage.none MassStorage.Reason.noDevice (.imm 0))
    ld 4 1 V.ids
    print MassStorage.Tag.ready 1
    st 4 M.step (.imm MassStorage.Step.configure)
    configure
    st 4 M.tag (.imm 0)
    st 4 M.blocksRead (.imm 0)
    inquiry err
    unitReady err unitReadyAttempts
    readCapacity err
    readMbr err rd
    readVolume err rd
    for h : i in [0:names.length] do
      lookup err rd i names[i] (i + 1 < names.length)
    readFile err rd
    quiesce
    halt
    readSubroutine err rd
    place err
    ld 4 1 M.step
    ld 4 2 M.reason
    emit (.alu .or 1 (.reg 2))
    print MassStorage.Tag.error 1
    ld 4 1 M.detail
    print MassStorage.Tag.errorDetail 1
    quiesce
    fail MassStorage.Fail.stopped

end LeanOS.Usb.Fat32
