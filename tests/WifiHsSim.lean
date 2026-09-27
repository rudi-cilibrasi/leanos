import LeanOS.Wifi.Handshake
import LeanOS.Wifi.Sim
import LeanOS.Wifi.Pbkdf2

/-! End-to-end simulation of the device 4-way handshake against a simulated
access point. The device model serves the PIO receive FIFO and captures the
PIO transmit FIFO; its authenticator is built from the reference library
(`Eapol`, `Aes`, `Pbkdf2`), independently of the device crypto. -/

open LeanOS.Wifi LeanOS.Wifi.Bytecode LeanOS.Wifi.Bytes

def bssid : ByteArray := ByteArray.mk #[0x02, 0x11, 0x22, 0x33, 0x44, 0x55]
def sta : ByteArray := ByteArray.mk Mlme.ourMac.data
def pmk : ByteArray := Pbkdf2.pmkOfPassphrase "correct horse".toUTF8 "QUAIL".toUTF8
def anonce : ByteArray := ByteArray.mk ((List.range 32).map (fun i => (0x30 + i).toUInt8)).toArray
def gtk : ByteArray := ByteArray.mk ((List.range 16).map (fun i => (0xa0 + i).toUInt8)).toArray
def rsnIe : ByteArray := Ieee80211.wpa2PskCcmpRsnIe

/-- Data frame from the AP to the station carrying `eapol`. -/
def fromAp (eapol : ByteArray) : ByteArray :=
  ByteArray.mk #[0x08, 0x02, 0, 0] ++ sta ++ bssid ++ bssid ++ ByteArray.mk #[0x10, 0x00] ++
    Ieee80211.llcSnap Ieee80211.ethertypeEapol ++ eapol

/-- PIO receive stream: 24-byte receive header (length = PLCP + MPDU + FCS),
6 PLCP bytes, MPDU, 4 FCS bytes. -/
def rxStream (mpdu : ByteArray) : ByteArray :=
  let len := 6 + mpdu.size + 4
  ByteArray.mk #[len.toUInt8, (len / 256).toUInt8] ++ zeros 22 ++ zeros 6 ++ mpdu ++ zeros 4

structure Ap where
  rxq : List ByteArray := []
  cur : Option (ByteArray × Nat) := none
  txCtl : UInt32 := 0
  txBuf : ByteArray := .empty
  log : Array String := #[]
  ptk : Option Eapol.Ptk := none
  done : Bool := false
  deriving Inhabited

def msg1 : ByteArray :=
  ({ protocolVersion := 2, keyInfo := 0x008a, keyLength := 16, replayCounter := 1, nonce := anonce,
     keyData := .empty } : Eapol.KeyFrame).encode

def handleTx (ap : Ap) (mpdu : ByteArray) : Ap := Id.run do
  let eapol := mpdu.extract 32 mpdu.size
  match Eapol.parseKeyFrame eapol with
  | none => return { ap with log := ap.log.push "tx: not EAPOL-Key" }
  | some f =>
    if f.keyInfo &&& Eapol.KeyInfo.secure == 0 then
      -- message 2
      let ptk := Eapol.derivePtk pmk bssid sta anonce f.nonce
      let micOk := Eapol.micValid ptk.kck eapol
      let rsnOk := Bytes.beq f.keyData rsnIe
      let kd := Eapol.padKeyData (rsnIe ++ Eapol.gtkKde 1 gtk)
      let wrapped := (Aes.keyWrap ptk.kek kd).getD .empty
      let m3 := (({ protocolVersion := 2, keyInfo := 0x13ca, keyLength := 16, replayCounter := 2,
                    nonce := anonce, keyData := wrapped } : Eapol.KeyFrame).sign ptk.kck).encode
      let addrOk := Bytes.beq (mpdu.extract 4 10) bssid && Bytes.beq (mpdu.extract 10 16) sta
      let line := s!"msg2: mic={micOk} rsn={rsnOk} addr={addrOk} replay={f.replayCounter}"
      let q := ap.rxq ++ [rxStream (fromAp m3)]
      return { ap with ptk := some ptk, rxq := q, log := ap.log.push line }
    else
      match ap.ptk with
      | none => return { ap with log := ap.log.push "msg4 before msg2" }
      | some ptk =>
        let micOk := Eapol.micValid ptk.kck eapol
        let line := s!"msg4: mic={micOk} replay={f.replayCounter} nonceZero={Bytes.beq f.nonce (zeros 32)}"
        return { ap with done := micOk, log := ap.log.push line }

def le32At (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i+1)).toUInt32 <<< 8) ||| ((b.get! (i+2)).toUInt32 <<< 16) |||
    ((b.get! (i+3)).toUInt32 <<< 24)

def device : Sim.Device Ap where
  read32 ap off :=
    if off == Mac.rxPioCtl then
      match ap.cur with
      | some _ => (3, ap)
      | none => (if ap.rxq.isEmpty then 0 else 1, ap)
    else if off == Mac.rxPioData then
      match ap.cur with
      | some (b, p) => (le32At (b ++ zeros 4) p, { ap with cur := some (b, p + 4) })
      | none => (0, ap)
    else (0, ap)
  read16 ap _ := (0, ap)
  write32 ap off v :=
    if off == Mac.rxPioCtl then
      if v == 1 then
        match ap.rxq with
        | b :: rest => { ap with cur := some (b, 0), rxq := rest }
        | [] => ap
      else if v == 2 then { ap with cur := none } else ap
    else if off == Mac.txPioCtl 1 then
      let ap := { ap with txCtl := v }
      if v &&& Mac.txCtlEof != 0 then
        let ap' := handleTx ap ap.txBuf
        { ap' with txBuf := .empty }
      else ap
    else if off == Mac.txPioData 1 then
      let n := if ap.txCtl &&& 0xF == 0xF then 4 else if ap.txCtl &&& 0xF == 7 then 3
               else if ap.txCtl &&& 0xF == 3 then 2 else 1
      let bytes := ByteArray.mk #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]
      { ap with txBuf := ap.txBuf ++ bytes.extract 0 n }
    else ap
  write16 ap _ _ := ap
  cfgRead32 ap _ := (0, ap)
  cfgWrite32 ap _ _ := ap

def send (n : Nat) : ProgM Unit := do
  li 11 Mlme.txMpdu
  li 12 n.toUInt32
  Mac.pioTx 1 11 12

def prog : ProgM Unit := do
  let L ← DevCrypto.install
  Mlme.putBytes "bssid" Mlme.bssidAt bssid
  Handshake.fourWay L pmk rsnIe send 50
  halt

def main : IO UInt32 := do
  match build prog with
  | .error e => IO.eprintln e; return 1
  | .ok p =>
    let (st, m) := Sim.run p device { rxq := [rxStream (fromAp msg1)] }
    for l in m.dev.log do IO.println l
    for (t, v) in m.prints do IO.println s!"print {String.ofList (Nat.toDigits 16 t.toNat)} {v}"
    -- GTK and TK in scratch must match the authenticator's
    let gtkOk := Bytes.beq (m.mem.extract Handshake.gtkAt.toNat (Handshake.gtkAt.toNat + 16)) gtk
    let tkOk := match m.dev.ptk with
      | some ptk => Bytes.beq (m.mem.extract Handshake.tkAt.toNat (Handshake.tkAt.toNat + 16)) ptk.tk
      | none => false
    IO.println s!"status {repr st} steps {m.steps} ap-done {m.dev.done} gtk {gtkOk} tk {tkOk}"
    return if st == .halt && m.dev.done && gtkOk && tkOk then 0 else 1
