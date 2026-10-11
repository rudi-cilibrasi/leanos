import LeanOS.Wifi.Responder
import LeanOS.Usb.Keyboard
import LeanOS.DeviceProgramConfinement
import LeanOS.Storage.Ahci
import LeanOS.Storage.AhciRead
import LeanOS.Net.Rtl8168
import LeanOS.Net.FrameSource
import LeanOS.Wifi.Endpoint

/-! Hosted generator: encodes a named Lean WiFi program into the binary image
consumed by `hardware/wifi/wifi-exec.h`.

Every image is confined: the program must pass
`LeanOS.DeviceProgramConfinement.admissible` under the admitted policy of its
target, which is then embedded in the version-3 header for the executor to
enforce.

usage: leanos-wifi-gen <program> <output.bin> [firmware-dir] -/

open LeanOS.Wifi.Bytecode LeanOS.Wifi.Bcm43224 LeanOS.Wifi.Driver

/-- The admitted policy for a program's target, if the target is admitted. -/
def admittedPolicy (p : Program) : Option Policy :=
  if p.effTarget == bcm43224Target then some LeanOS.DeviceProgramConfinement.qotomBcm43224Policy
  else if p.effTarget == @LeanOS.Usb.Xhci.target LeanOS.Usb.Xhci.bayTrail then
    some LeanOS.DeviceProgramConfinement.qotomXhciPolicy
  else if p.effTarget == @LeanOS.Usb.Xhci.target LeanOS.Usb.Xhci.qemu then
    some LeanOS.DeviceProgramConfinement.q35XhciPolicy
  else if p.effTarget == LeanOS.Storage.Ahci.target then
    some LeanOS.DeviceProgramConfinement.qotomAhciPolicy
  else if p.effTarget == LeanOS.Storage.AhciRead.target then
    some LeanOS.DeviceProgramConfinement.q35AhciPolicy
  else if p.effTarget == LeanOS.Net.Rtl8168.target then
    some LeanOS.DeviceProgramConfinement.qotomRtl8168Policy
  else if p.effTarget == LeanOS.Net.FrameSource.target then
    some LeanOS.DeviceProgramConfinement.q35FrameSourcePolicy
  else none

/-- Check `p` against its target's policy and attach the policy. -/
def admit (p : Program) : Except String Program := do
  let some π := admittedPolicy p | throw s!"no admitted policy for target {repr p.effTarget}"
  let p := { p with policy := some π }
  if LeanOS.DeviceProgramConfinement.admissible p π then
    return p
  let at_ := LeanOS.DeviceProgramConfinement.firstViolation p π
  let what := match at_ with
    | some i => s!"instruction {i}: {repr p.words[i]!}"
    | none => "target window exceeds the policy window"
  throw s!"program is not admissible under its policy ({what})"

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
   ("scan5", scanProg fwDir 5), ("scan6", scanProg fwDir 6), ("scan7", scanProg fwDir 7),
   ("scan8", scanProg fwDir 8), ("scan13", scanProg fwDir 13),
   ("raw11", do
      let cfg := LeanOS.Wifi.NPhy.qotom 11
      return listen (← loadFirmware fwDir) (phyInitFull cfg) 8 24 4000),
   ("connect", do
      let psk ← IO.getEnv "LEANOS_WIFI_PSK"
      let some psk := psk | throw (IO.userError "set LEANOS_WIFI_PSK")
      let pmk := LeanOS.Wifi.Pbkdf2.pmkOfPassphrase psk.toUTF8 "QUAIL".toUTF8
      let bssidHex := (← IO.getEnv "LEANOS_WIFI_BSSID").getD "c4f174138a47"
      let bssid := ByteArray.mk ((List.range 6).map fun i =>
        ((LeanOS.Wifi.NPhy.hexU32s (bssidHex.drop (2*i) |>.take 2).toString).getD 0 0).toUInt8).toArray
      if bssid.size != 6 || bssidHex.length != 12 then throw (IO.userError "bad LEANOS_WIFI_BSSID")
      let fw ← loadFirmware fwDir
      let full := (← IO.getEnv "LEANOS_WIFI_DHCP").isSome
      let serve := (← IO.getEnv "LEANOS_WIFI_SERVE_SECONDS").bind String.toNat?
      let chain := (← IO.getEnv "LEANOS_WIFI_TXCHAIN").bind String.toNat?
      let cal := ((← IO.getEnv "LEANOS_WIFI_CAL").bind String.toNat?).getD
        (LeanOS.Wifi.NPhy.qotom 6).calLevel
      let base : LeanOS.Wifi.NPhy.PhyCfg := { LeanOS.Wifi.NPhy.qotom 6 with calLevel := cal }
      let cfg6 : LeanOS.Wifi.NPhy.PhyCfg :=
        match chain with
        | some c => { base with txChainOverride := some c }
        | none => base
      -- LEANOS_WIFI_NETWORK_SUBJECT: serve the frame endpoint of the ring-3
      -- network subject (issue #450) instead of answering in the driver.
      let endpoint := (← IO.getEnv "LEANOS_WIFI_NETWORK_SUBJECT").isSome
      return if let some secs := serve then
               if endpoint then
                 LeanOS.Wifi.Endpoint.connectAndServe fw cfg6 bssid pmk
                   (secs * 1000000).toUInt32
               else
                 LeanOS.Wifi.Responder.connectAndServe fw cfg6 bssid pmk
                   (secs * 1000000).toUInt32
             else if full then LeanOS.Wifi.Connect.connectDhcp fw cfg6 bssid pmk
             else connect fw (LeanOS.Wifi.NPhy.qotom 6) bssid pmk),
   ("ahci-identify", pure LeanOS.Storage.Ahci.program),
   ("net-q35-frames", pure LeanOS.Net.FrameSource.program),
   ("net-bcm-frames", pure LeanOS.Net.FrameSource.bcmProgram),
   ("ahci-q35-service", pure LeanOS.Storage.AhciRead.program),
   ("rtl8168-arp", pure LeanOS.Net.Rtl8168.program),
   ("kbd", do
      let secs := ((← IO.getEnv "LEANOS_KBD_SECONDS").bind String.toNat?).getD 60
      let idle := ((← IO.getEnv "LEANOS_KBD_IDLE").bind String.toNat?).getD 0
      return @LeanOS.Usb.Keyboard.program LeanOS.Usb.Xhci.bayTrail secs.toUInt32 idle.toUInt32 false false),
   ("kbd-service", do
      let secs := ((← IO.getEnv "LEANOS_KBD_SECONDS").bind String.toNat?).getD 60
      let idle := ((← IO.getEnv "LEANOS_KBD_IDLE").bind String.toNat?).getD 0
      let trace := (← IO.getEnv "LEANOS_KBD_TRACE").isSome
      return @LeanOS.Usb.Keyboard.program LeanOS.Usb.Xhci.bayTrail secs.toUInt32 idle.toUInt32 true trace),
   ("kbd-q35-service", do
      let secs := ((← IO.getEnv "LEANOS_KBD_SECONDS").bind String.toNat?).getD 10
      return @LeanOS.Usb.Keyboard.program LeanOS.Usb.Xhci.qemu secs.toUInt32 0 true false),
   ("kbd-q35", do
      let secs := ((← IO.getEnv "LEANOS_KBD_SECONDS").bind String.toNat?).getD 10
      let idle := ((← IO.getEnv "LEANOS_KBD_IDLE").bind String.toNat?).getD 0
      return @LeanOS.Usb.Keyboard.program LeanOS.Usb.Xhci.qemu secs.toUInt32 idle.toUInt32 false false),
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
      match build (← mk) >>= admit with
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
