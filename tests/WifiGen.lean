import LeanOS.Wifi.Driver

/-! Hosted generator: encodes a named Lean WiFi program into the binary image
consumed by `hardware/wifi/wifi-exec.h`.

usage: leanos-wifi-gen <program> <output.bin> [firmware-dir] -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Driver

/-- Split the brcmsmac firmware container (`bcm43xx-0.fw` with its
`bcm43xx_hdr-0.fw` index of {offset, length, id} little-endian words). -/
def loadFirmware (dir : System.FilePath) : IO Firmware := do
  let data ← IO.FS.readBinFile (dir / "bcm43xx-0.fw")
  let hdr ← IO.FS.readBinFile (dir / "bcm43xx_hdr-0.fw")
  let entry (id : UInt32) : IO ByteArray := do
    for k in [0:hdr.size / 12] do
      if le32 hdr (12 * k + 8) == id then
        let off := (le32 hdr (12 * k)).toNat
        let len := (le32 hdr (12 * k + 4)).toNat
        if off + len > data.size then throw (IO.userError s!"firmware entry {id} out of range")
        return data.extract off (off + len)
    throw (IO.userError s!"firmware entry {id} missing")
  -- ucode_loader.c ids: 8 N0BSINITVALS16, 9 N0INITVALS16, 10 UCODE16_MIMO.
  return { ucode := ← entry 10, initvals := ← entry 9, bsinitvals := ← entry 8 }

/-- Scan one channel: full bring-up, PIO receive of up to 30 frames with a
4 s idle timeout, then the microcode receive counters. -/
def scanProg (fwDir : System.FilePath) (ch : Nat) : IO (ProgM Unit) := do
  let cfg := LeanOS.Wifi.NPhy.qotom ch
  let fw ← loadFirmware fwDir
  return (do bringUp; ucodeStart fw; LeanOS.Wifi.Mac.coreInitTail
             LeanOS.Wifi.Mac.bandInit fw (phyInitFull cfg)
             LeanOS.Wifi.Mac.enableMacPromisc
             LeanOS.Wifi.Mac.rxBeacons 40 3000 30
             for k in [0:0x40] do
               shmRead16 0 (0xE0 + 2 * k.toUInt32); print (0x0900 + k.toUInt32) 0
             printImm Tag.done 0; halt)

def programs (fwDir : System.FilePath) : List (String × IO (ProgM Unit)) :=
  [("probe", pure probe), ("sprom", pure spromDump),
   ("tables", pure (tableCheck (LeanOS.Wifi.NPhy.qotom 6))),
   ("tblexp", pure tableExperiment), ("radio1", pure (radioTest (LeanOS.Wifi.NPhy.qotom 1))), ("tblexp2", pure tableExperiment2),
   ("ucode", do return ucodeBoot (← loadFirmware fwDir)),
   ("listen1p", do
      let cfg := LeanOS.Wifi.NPhy.qotom 1
      return listen (← loadFirmware fwDir) (phyInitPartial cfg) 20 12 3000),
   ("stats1p", do
      let cfg := LeanOS.Wifi.NPhy.qotom 1
      return listenStats (← loadFirmware fwDir) (phyInitPartial cfg)),
   ("stats1q", do
      let cfg := LeanOS.Wifi.NPhy.qotom 1
      return listenStats (← loadFirmware fwDir) (phyInitPartial2 cfg)),
   ("act1q", do
      let cfg := LeanOS.Wifi.NPhy.qotom 1
      return listenActivity (← loadFirmware fwDir) (phyInitPartial2 cfg)),
   ("stats1", do
      let cfg := LeanOS.Wifi.NPhy.qotom 1
      return listenStats (← loadFirmware fwDir) (phyInitFull cfg)),
   ("scan1", scanProg fwDir 1), ("scan2", scanProg fwDir 2), ("scan3", scanProg fwDir 3),
   ("scan4", scanProg fwDir 4), ("scan9", scanProg fwDir 9), ("scan10", scanProg fwDir 10),
   ("scan11", scanProg fwDir 11), ("scan12", scanProg fwDir 12),
   ("raw11", do
      let cfg := LeanOS.Wifi.NPhy.qotom 11
      return listen (← loadFirmware fwDir) (phyInitFull cfg) 8 24 4000),
   ("scanOld1", do
      let cfg := LeanOS.Wifi.NPhy.qotom 1
      let fw ← loadFirmware fwDir
      return (do bringUp; ucodeStart fw; LeanOS.Wifi.Mac.coreInitTail
                 LeanOS.Wifi.Mac.bandInit fw (phyInitFull cfg)
                 LeanOS.Wifi.Mac.enableMacPromisc
                 LeanOS.Wifi.Mac.rxBeacons 40 3000 24
                 printImm Tag.done 0; halt))]

def main (args : List String) : IO UInt32 := do
  match args with
  | [name, out] | [name, out, _] =>
    let fwDir := (args.drop 2).headD "build/wifi/fw"
    match (programs fwDir).lookup name with
    | none =>
      IO.eprintln s!"unknown program {name}; known: {(programs fwDir).map (·.1)}"
      return 2
    | some mk =>
      match build (← mk) with
      | .error e => IO.eprintln s!"build failed: {e}"; return 1
      | .ok prog =>
        IO.FS.writeBinFile out prog.image
        IO.println s!"{name}: {prog.words.size} instructions, {prog.blob.size} blob bytes -> {out}"
        for (sec, off, len) in prog.sections do
          IO.println s!"  blob {sec} @0x{String.ofList (Nat.toDigits 16 off)} len {len}"
        return 0
  | _ =>
    IO.eprintln "usage: leanos-wifi-gen <program> <output.bin>"
    return 2
