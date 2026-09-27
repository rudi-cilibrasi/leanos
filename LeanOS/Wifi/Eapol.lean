import LeanOS.Wifi.Sha1
import LeanOS.Wifi.Aes

/-!
# IEEE 802.11i / RSN key management for a WPA2-PSK supplicant

* `prf`: the HMAC-SHA1 based PRF of IEEE 802.11-2016 12.7.1.2.
* `derivePtk`: PTK = PRF-384(PMK, "Pairwise key expansion",
  Min(AA,SPA) ‖ Max(AA,SPA) ‖ Min(ANonce,SNonce) ‖ Max(ANonce,SNonce)),
  split into KCK (16), KEK (16) and TK (16, CCMP).
* EAPOL-Key frame codec (key descriptor type 2 = RSN) and MIC for key
  descriptor version 2 (HMAC-SHA1-128, key data wrapped with AES key wrap).
* A pure supplicant state machine for the 4-way handshake.

Randomness (the SNonce) is an input: the caller supplies it in `Config`.
-/

namespace LeanOS.Wifi.Eapol

open LeanOS.Wifi.Bytes

/-! ## PRF and PTK -/

/-- `PRF-(8·len)(K, A, B)`: concatenated `HMAC-SHA1(K, A ‖ 0x00 ‖ B ‖ i)`, truncated. -/
def prf (key : ByteArray) (label : String) (data : ByteArray) (len : Nat) : ByteArray := Id.run do
  let hk := Sha1.HmacKey.ofKey key
  let prefix_ := label.toUTF8.push 0 ++ data
  let mut out := ByteArray.emptyWithCapacity (len + 20)
  let mut i : Nat := 0
  while out.size < len do
    out := out ++ hk.mac (prefix_.push i.toUInt8)
    i := i + 1
  return out.extract 0 len

structure Ptk where
  kck : ByteArray
  kek : ByteArray
  tk : ByteArray

def minMax (a b : ByteArray) : ByteArray :=
  if Bytes.lt a b then a ++ b else b ++ a

/-- PTK for CCMP (PRF-384). `aa` is the authenticator (AP) MAC, `spa` ours. -/
def derivePtk (pmk aa spa anonce snonce : ByteArray) : Ptk :=
  let p := prf pmk "Pairwise key expansion" (minMax aa spa ++ minMax anonce snonce) 48
  { kck := slice p 0 16, kek := slice p 16 16, tk := slice p 32 16 }

/-! ## EAPOL-Key frames -/

def eapolTypeKey : UInt8 := 3
def descriptorRsn : UInt8 := 2

namespace KeyInfo
def versionMask : UInt16 := 0x0007
/-- Key descriptor version 2: HMAC-SHA1-128 MIC, AES key wrap. -/
def versionHmacSha1Aes : UInt16 := 0x0002
def pairwise : UInt16 := 0x0008
def install : UInt16 := 0x0040
def ack : UInt16 := 0x0080
def mic : UInt16 := 0x0100
def secure : UInt16 := 0x0200
def error : UInt16 := 0x0400
def request : UInt16 := 0x0800
def encryptedKeyData : UInt16 := 0x1000
end KeyInfo

/-- An EAPOL packet carrying an RSN EAPOL-Key descriptor. -/
structure KeyFrame where
  protocolVersion : UInt8
  descriptorType : UInt8 := descriptorRsn
  keyInfo : UInt16
  keyLength : UInt16
  replayCounter : UInt64
  nonce : ByteArray
  iv : ByteArray := zeros 16
  rsc : ByteArray := zeros 8
  reserved : ByteArray := zeros 8
  mic : ByteArray := zeros 16
  keyData : ByteArray

/-- Offset of the MIC field within the whole EAPOL packet (4-byte header + 77). -/
def micOffset : Nat := 81

/-- Size of the EAPOL-Key body before the key data. -/
def fixedBodyLen : Nat := 95

private def fixed (b : ByteArray) (n : Nat) : ByteArray :=
  take (b ++ zeros n) n

/-- Serialise as a complete EAPOL packet (version, type 3, length, body). -/
def KeyFrame.encode (f : KeyFrame) : ByteArray :=
  let body := concat [ByteArray.mk #[f.descriptorType], u16be f.keyInfo, u16be f.keyLength,
    u64be f.replayCounter, fixed f.nonce 32, fixed f.iv 16, fixed f.rsc 8, fixed f.reserved 8,
    fixed f.mic 16, u16be f.keyData.size.toUInt16, f.keyData]
  ByteArray.mk #[f.protocolVersion, eapolTypeKey] ++ u16be body.size.toUInt16 ++ body

/-- Parse an EAPOL packet as an RSN EAPOL-Key frame. Trailing bytes beyond
the EAPOL body length (link-layer padding) are ignored. -/
def parseKeyFrame (b : ByteArray) : Option KeyFrame := do
  if b.size < 4 + fixedBodyLen then none
  if at! b 1 != eapolTypeKey then none
  let bodyLen := (getU16be b 2).toNat
  if bodyLen < fixedBodyLen || 4 + bodyLen > b.size then none
  let dataLen := (getU16be b (4 + 93)).toNat
  if fixedBodyLen + dataLen > bodyLen then none
  return { protocolVersion := at! b 0, descriptorType := at! b 4, keyInfo := getU16be b 5,
           keyLength := getU16be b 7, replayCounter := getU64be b 9, nonce := slice b 17 32,
           iv := slice b 49 16, rsc := slice b 65 8, reserved := slice b 73 8,
           mic := slice b micOffset 16, keyData := slice b (4 + fixedBodyLen) dataLen }

/-- HMAC-SHA1-128 over the EAPOL packet with the MIC field zeroed. -/
def computeMic (kck packet : ByteArray) : ByteArray :=
  take (Sha1.hmac kck (overwrite packet micOffset (zeros 16))) 16

/-- Set the MIC of `f` computed with `kck`. -/
def KeyFrame.sign (f : KeyFrame) (kck : ByteArray) : KeyFrame :=
  { f with mic := computeMic kck { f with mic := zeros 16 }.encode }

/-- Verify the MIC of a raw EAPOL packet (as received, up to its body length). -/
def micValid (kck packet : ByteArray) : Bool :=
  let len := 4 + (getU16be packet 2).toNat
  let p := take packet len
  p.size ≥ micOffset + 16 && ctEq (computeMic kck p) (slice p micOffset 16)

/-! ## Key data elements (IEs and KDEs) -/

/-- A GTK from a GTK KDE (OUI 00-0F-AC, data type 1). -/
structure Gtk where
  keyId : UInt8
  tx : Bool
  key : ByteArray

/-- Split decrypted key data into elements; stops at the `0xdd 0x00…` padding. -/
def keyDataElements (b : ByteArray) : Option (List (UInt8 × ByteArray)) :=
  let rec go (fuel : Nat) (off : Nat) (acc : List (UInt8 × ByteArray)) :
      Option (List (UInt8 × ByteArray)) :=
    match fuel with
    | 0 => some acc.reverse
    | fuel + 1 =>
      if off + 2 > b.size then some acc.reverse
      else
        let id := at! b off
        let len := (at! b (off + 1)).toNat
        if id == 0xdd && len == 0 then some acc.reverse
        else if off + 2 + len > b.size then none
        else go fuel (off + 2 + len) ((id, slice b (off + 2) len) :: acc)
  go b.size 0 []

/-- Find the GTK KDE among key data elements. -/
def findGtk (elems : List (UInt8 × ByteArray)) : Option Gtk :=
  elems.findSome? fun (id, body) =>
    if id == 0xdd && body.size ≥ 6 && at! body 0 == 0x00 && at! body 1 == 0x0F &&
        at! body 2 == 0xAC && at! body 3 == 0x01 then
      some { keyId := at! body 4 &&& 0x03, tx := at! body 4 &&& 0x04 != 0, key := drop body 6 }
    else none

/-- Encode a GTK KDE (used by test authenticators). -/
def gtkKde (keyId : UInt8) (gtk : ByteArray) : ByteArray :=
  concat [ByteArray.mk #[0xdd, (6 + gtk.size).toUInt8, 0x00, 0x0F, 0xAC, 0x01, keyId &&& 3, 0], gtk]

/-- Pad key data before AES key wrap (802.11-2016 12.7.2): `0xdd` then zeros,
up to a multiple of 8 bytes and at least 16 bytes. -/
def padKeyData (b : ByteArray) : ByteArray :=
  if b.size ≥ 16 && b.size % 8 == 0 then b
  else
    let target := max 16 ((b.size + 1 + 7) / 8 * 8)
    b.push 0xdd ++ zeros (target - b.size - 1)

/-! ## 4-way handshake supplicant -/

structure Config where
  pmk : ByteArray
  /-- Authenticator (AP) MAC address. -/
  aa : ByteArray
  /-- Supplicant (our) MAC address. -/
  spa : ByteArray
  /-- 32 random bytes chosen by the caller. -/
  snonce : ByteArray
  /-- Our RSN element (sent in message 2; must match the association request). -/
  rsnIe : ByteArray
  /-- The AP's RSN element from its beacon/probe response; if present,
  message 3 must carry exactly this element. -/
  apRsnIe : Option ByteArray := none
  /-- EAPOL protocol version used in our frames. -/
  eapolVersion : UInt8 := 1

structure InstalledKeys where
  ptk : Ptk
  gtk : Gtk
  /-- Receive sequence counter for the GTK from message 3. -/
  gtkRsc : ByteArray

def InstalledKeys.tk (k : InstalledKeys) : ByteArray := k.ptk.tk

inductive Phase where
  | waitMsg1
  | waitMsg3 (anonce : ByteArray) (ptk : Ptk)
  | complete (anonce : ByteArray) (keys : InstalledKeys)

structure Supplicant where
  cfg : Config
  phase : Phase := .waitMsg1
  /-- Local replay counter: the largest counter seen in an accepted message. -/
  replay : Option UInt64 := none

inductive Error where
  | malformed
  | unsupportedDescriptor
  | unexpectedMessage
  | replayed
  | badMic
  | anonceMismatch
  | unwrapFailed
  | rsnIeMismatch
  | missingGtk
  deriving BEq, Repr

inductive Output where
  /-- Transmit message 2. -/
  | sendMsg2 (frame : ByteArray)
  /-- Transmit message 4, then install the pairwise and group keys. -/
  | sendMsg4 (frame : ByteArray) (keys : InstalledKeys)
  /-- Retransmit message 4 for a repeated message 3 after keys are installed.
  The keys must NOT be reinstalled (that would reset the CCMP packet number;
  cf. the 2017 key-reinstallation attacks). -/
  | resendMsg4 (frame : ByteArray)

def Supplicant.init (cfg : Config) : Supplicant := { cfg }

private def replayOk (local_ : Option UInt64) (rc : UInt64) : Bool :=
  match local_ with
  | none => true
  | some l => rc > l

private def rsnIeOf (elems : List (UInt8 × ByteArray)) : Option ByteArray :=
  (elems.find? (·.1 == 0x30)).map fun (_, body) => ByteArray.mk #[0x30, body.size.toUInt8] ++ body

private def handleMsg1 (s : Supplicant) (f : KeyFrame) : Except Error (Supplicant × Output) := do
  if !replayOk s.replay f.replayCounter then throw .replayed
  let ptk := derivePtk s.cfg.pmk s.cfg.aa s.cfg.spa f.nonce s.cfg.snonce
  let msg2 : KeyFrame :=
    { protocolVersion := s.cfg.eapolVersion,
      keyInfo := KeyInfo.versionHmacSha1Aes ||| KeyInfo.pairwise ||| KeyInfo.mic,
      keyLength := 0, replayCounter := f.replayCounter, nonce := s.cfg.snonce,
      keyData := s.cfg.rsnIe }
  -- Message 1 carries no MIC, so it does not advance the local replay counter.
  return ({ s with phase := .waitMsg3 f.nonce ptk }, .sendMsg2 (msg2.sign ptk.kck).encode)

private def handleMsg3 (s : Supplicant) (raw : ByteArray) (f : KeyFrame) (anonce : ByteArray)
    (ptk : Ptk) : Except Error (Supplicant × Output) := do
  if !replayOk s.replay f.replayCounter then throw .replayed
  if !micValid ptk.kck raw then throw .badMic
  if !beq f.nonce anonce then throw .anonceMismatch
  if f.keyInfo &&& KeyInfo.encryptedKeyData == 0 then throw .malformed
  let plain ← match Aes.keyUnwrap ptk.kek f.keyData with
    | some p => pure p
    | none => throw .unwrapFailed
  let elems ← match keyDataElements plain with
    | some e => pure e
    | none => throw .malformed
  if let some expected := s.cfg.apRsnIe then
    match rsnIeOf elems with
    | some ie => if !beq ie expected then throw .rsnIeMismatch
    | none => throw .rsnIeMismatch
  let gtk ← match findGtk elems with
    | some g => pure g
    | none => throw .missingGtk
  let keys : InstalledKeys := { ptk, gtk, gtkRsc := f.rsc }
  let msg4 : KeyFrame :=
    { protocolVersion := s.cfg.eapolVersion,
      keyInfo := KeyInfo.versionHmacSha1Aes ||| KeyInfo.pairwise ||| KeyInfo.mic ||| KeyInfo.secure,
      keyLength := 0, replayCounter := f.replayCounter, nonce := zeros 32, keyData := ByteArray.empty }
  return ({ s with phase := .complete anonce keys, replay := some f.replayCounter },
          .sendMsg4 (msg4.sign ptk.kck).encode keys)

/-- Process one received EAPOL packet (the LLC/SNAP payload with ethertype 0x888E). -/
def Supplicant.handle (s : Supplicant) (raw : ByteArray) : Except Error (Supplicant × Output) := do
  let f ← match parseKeyFrame raw with
    | some f => pure f
    | none => throw .malformed
  if f.descriptorType != descriptorRsn then throw .unsupportedDescriptor
  if f.keyInfo &&& KeyInfo.versionMask != KeyInfo.versionHmacSha1Aes then
    throw .unsupportedDescriptor
  let ki := f.keyInfo
  if ki &&& KeyInfo.pairwise == 0 || ki &&& KeyInfo.ack == 0 then throw .unexpectedMessage
  if ki &&& KeyInfo.mic == 0 then
    handleMsg1 s f
  else
    match s.phase with
    | .waitMsg3 anonce ptk => handleMsg3 s raw f anonce ptk
    -- A retransmitted message 3 after completion is answered again, without
    -- reinstalling keys; the installed keys are kept.
    | .complete anonce keys => do
      let (s', out) ← handleMsg3 s raw f anonce keys.ptk
      match out with
      | .sendMsg4 frame _ => return ({ s' with phase := .complete anonce keys }, .resendMsg4 frame)
      | other => return (s', other)
    | .waitMsg1 => throw .unexpectedMessage

end LeanOS.Wifi.Eapol
