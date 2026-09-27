import LeanOS.Wifi.Aes

/-!
# IEEE 802.11 frame codecs for a WPA2-PSK (CCMP) station

Pure builders and parsers for the frames a non-AP station needs to scan,
authenticate (open system), associate with RSN, carry EAPOL and IPv4 over
LLC/SNAP, and protect data MPDUs with CCMP (IEEE 802.11-2016 12.5.3).

Frames here exclude the FCS; the hardware appends and checks it.
Multi-byte 802.11 fields are little-endian; LLC/SNAP ethertypes are big-endian.
-/

namespace LeanOS.Wifi.Ieee80211

open LeanOS.Wifi.Bytes

/-- A 6-byte MAC address. -/
abbrev Mac := ByteArray

def broadcastMac : Mac := replicate 6 0xff

/-! ## Frame control -/

namespace FrameType
def mgmt : UInt8 := 0
def ctrl : UInt8 := 1
def data : UInt8 := 2
end FrameType

namespace MgmtSubtype
def assocReq : UInt8 := 0
def assocResp : UInt8 := 1
def probeReq : UInt8 := 4
def probeResp : UInt8 := 5
def beacon : UInt8 := 8
def disassoc : UInt8 := 10
def auth : UInt8 := 11
def deauth : UInt8 := 12
end MgmtSubtype

namespace DataSubtype
def data : UInt8 := 0
def qosData : UInt8 := 8
end DataSubtype

-- Frame control flag bits (second octet).
namespace Flags
def toDS : UInt8 := 0x01
def fromDS : UInt8 := 0x02
def moreFrag : UInt8 := 0x04
def retry : UInt8 := 0x08
def pwrMgt : UInt8 := 0x10
def moreData : UInt8 := 0x20
def protectedFrame : UInt8 := 0x40
def order : UInt8 := 0x80
end Flags

structure FrameControl where
  ftype : UInt8
  subtype : UInt8
  flags : UInt8
  deriving BEq, Repr

def FrameControl.encode (fc : FrameControl) : ByteArray :=
  ByteArray.mk #[((fc.subtype &&& 0x0f) <<< 4) ||| ((fc.ftype &&& 0x03) <<< 2), fc.flags]

def FrameControl.decode (b : ByteArray) : FrameControl :=
  let b0 := at! b 0
  { ftype := (b0 >>> 2) &&& 0x03, subtype := b0 >>> 4, flags := at! b 1 }

def FrameControl.has (fc : FrameControl) (flag : UInt8) : Bool := fc.flags &&& flag != 0

/-- Sequence control value for sequence number `seq` (12 bits), fragment 0. -/
def seqCtl (seq : UInt16) : UInt16 := (seq &&& 0x0fff) <<< 4

/-- Generic three-address header: FC, duration, A1, A2, A3, sequence control. -/
def header3 (fc : FrameControl) (duration : UInt16) (a1 a2 a3 : Mac) (seq : UInt16) : ByteArray :=
  concat [fc.encode, u16le duration, take a1 6, take a2 6, take a3 6, u16le (seqCtl seq)]

/-- Management frame header (DA, SA, BSSID). -/
def mgmtHeader (subtype : UInt8) (da sa bssid : Mac) (seq : UInt16) : ByteArray :=
  header3 { ftype := FrameType.mgmt, subtype, flags := 0 } 0 da sa bssid seq

/-- A parsed management frame. -/
structure MgmtFrame where
  fc : FrameControl
  da : Mac
  sa : Mac
  bssid : Mac
  seqCtl : UInt16
  body : ByteArray

def parseMgmt (frame : ByteArray) : Option MgmtFrame :=
  if frame.size < 24 then none else
  let fc := FrameControl.decode frame
  if fc.ftype != FrameType.mgmt then none else
  some { fc, da := slice frame 4 6, sa := slice frame 10 6, bssid := slice frame 16 6,
         seqCtl := getU16le frame 22, body := drop frame 24 }

/-! ## Information elements -/

namespace IeId
def ssid : UInt8 := 0
def supportedRates : UInt8 := 1
def dsParams : UInt8 := 3
def rsn : UInt8 := 48
def extendedRates : UInt8 := 50
def vendor : UInt8 := 221
end IeId

/-- Encode an information element. Bodies longer than 255 bytes are truncated. -/
def ie (id : UInt8) (body : ByteArray) : ByteArray :=
  let body := take body 255
  ByteArray.mk #[id, body.size.toUInt8] ++ body

/-- Split an IE sequence into `(id, body)` pairs; `none` if an IE is truncated. -/
def parseIes (b : ByteArray) : Option (List (UInt8 × ByteArray)) :=
  let rec go (fuel : Nat) (off : Nat) (acc : List (UInt8 × ByteArray)) :
      Option (List (UInt8 × ByteArray)) :=
    match fuel with
    | 0 => some acc.reverse
    | fuel + 1 =>
      if off == b.size then some acc.reverse
      else if off + 2 > b.size then none
      else
        let len := (at! b (off + 1)).toNat
        if off + 2 + len > b.size then none
        else go fuel (off + 2 + len) ((at! b off, slice b (off + 2) len) :: acc)
  go b.size 0 []

def findIe (ies : List (UInt8 × ByteArray)) (id : UInt8) : Option ByteArray :=
  (ies.find? (·.1 == id)).map (·.2)

/-- Rates in 500 kb/s units: 1, 2, 5.5, 11, 6, 9, 12, 18 Mb/s (Supported Rates IE). -/
def supportedRates : ByteArray := ByteArray.mk #[0x02, 0x04, 0x0b, 0x16, 0x0c, 0x12, 0x18, 0x24]

/-- 24, 36, 48, 54 Mb/s (Extended Supported Rates IE). -/
def extendedRates : ByteArray := ByteArray.mk #[0x30, 0x48, 0x60, 0x6c]

/-! ## RSN element -/

/-- A cipher/AKM suite selector packed as `OUI << 8 ||| type`. -/
abbrev Suite := UInt32

def suite (b : ByteArray) (off : Nat) : Suite := getU32be b off

namespace Suites
def ccmp : Suite := 0x000FAC04
def tkip : Suite := 0x000FAC02
def akmPsk : Suite := 0x000FAC02
def akm8021x : Suite := 0x000FAC01
end Suites

structure RsnInfo where
  version : UInt16
  groupCipher : Suite
  pairwiseCiphers : List Suite
  akms : List Suite
  capabilities : UInt16
  deriving BEq, Repr

/-- True when the network offers WPA2-PSK with CCMP pairwise and group ciphers. -/
def RsnInfo.isWpa2PskCcmp (r : RsnInfo) : Bool :=
  r.version == 1 && r.groupCipher == Suites.ccmp &&
    r.pairwiseCiphers.contains Suites.ccmp && r.akms.contains Suites.akmPsk

/-- Parse an RSN element body (without the id/length octets). Optional
trailing fields default as in 802.11-2016 9.4.2.25 (CCMP / 802.1X). -/
def parseRsn (b : ByteArray) : Option RsnInfo := do
  if b.size < 2 then none
  let version := getU16le b 0
  if b.size < 6 then
    return { version, groupCipher := Suites.ccmp, pairwiseCiphers := [Suites.ccmp],
             akms := [Suites.akm8021x], capabilities := 0 }
  let group := suite b 2
  let readList (off : Nat) : Option (List Suite × Nat) :=
    if off + 2 > b.size then none else
    let n := (getU16le b off).toNat
    if off + 2 + 4 * n > b.size then none else
    some ((List.range n).map (fun i => suite b (off + 2 + 4 * i)), off + 2 + 4 * n)
  if b.size < 8 then
    return { version, groupCipher := group, pairwiseCiphers := [Suites.ccmp],
             akms := [Suites.akm8021x], capabilities := 0 }
  let (pairwise, off) ← readList 6
  if off + 2 > b.size then
    return { version, groupCipher := group, pairwiseCiphers := pairwise,
             akms := [Suites.akm8021x], capabilities := 0 }
  let (akms, off) ← readList off
  let caps := if off + 2 ≤ b.size then getU16le b off else 0
  return { version, groupCipher := group, pairwiseCiphers := pairwise, akms, capabilities := caps }

/-- Our RSN element (id and length included): version 1, group CCMP,
pairwise CCMP, AKM PSK, capabilities 0. -/
def wpa2PskCcmpRsnIe : ByteArray :=
  ByteArray.mk #[0x30, 0x14, 0x01, 0x00, 0x00, 0x0F, 0xAC, 0x04, 0x01, 0x00, 0x00, 0x0F, 0xAC,
    0x04, 0x01, 0x00, 0x00, 0x0F, 0xAC, 0x02, 0x00, 0x00]

/-! ## Scanning -/

/-- Probe request: wildcard or directed SSID, rates, extended rates, DS parameter. -/
def probeRequest (sa : Mac) (ssid : ByteArray) (channel : UInt8) (seq : UInt16) : ByteArray :=
  concat [mgmtHeader MgmtSubtype.probeReq broadcastMac sa broadcastMac seq,
    ie IeId.ssid ssid, ie IeId.supportedRates supportedRates,
    ie IeId.extendedRates extendedRates, ie IeId.dsParams (ByteArray.mk #[channel])]

/-- What a station learns from a beacon or probe response. -/
structure BssInfo where
  bssid : Mac
  beaconInterval : UInt16
  capability : UInt16
  ssid : ByteArray
  channel : Option UInt8
  rsn : Option RsnInfo
  /-- The raw RSN element including id/length, for the message-3 comparison. -/
  rsnIe : Option ByteArray

/-- Parse a beacon or probe response. -/
def parseBeacon (frame : ByteArray) : Option BssInfo := do
  let m ← parseMgmt frame
  if m.fc.subtype != MgmtSubtype.beacon && m.fc.subtype != MgmtSubtype.probeResp then none
  if m.body.size < 12 then none
  let ies ← parseIes (drop m.body 12)
  let ssid := (findIe ies IeId.ssid).getD ByteArray.empty
  let channel := (findIe ies IeId.dsParams).bind fun b => if b.size ≥ 1 then some (at! b 0) else none
  let rsnBody := findIe ies IeId.rsn
  let rsn := rsnBody.bind parseRsn
  return { bssid := m.bssid, beaconInterval := getU16le m.body 8, capability := getU16le m.body 10,
           ssid, channel, rsn, rsnIe := rsnBody.map (ie IeId.rsn) }

/-! ## Authentication and association -/

/-- Open System authentication request (algorithm 0, transaction 1, status 0). -/
def authRequest (sa bssid : Mac) (seq : UInt16) : ByteArray :=
  mgmtHeader MgmtSubtype.auth bssid sa bssid seq ++ u16le 0 ++ u16le 1 ++ u16le 0

structure AuthFrame where
  algorithm : UInt16
  transaction : UInt16
  status : UInt16
  deriving BEq, Repr

def parseAuth (frame : ByteArray) : Option AuthFrame := do
  let m ← parseMgmt frame
  if m.fc.subtype != MgmtSubtype.auth || m.body.size < 6 then none
  return { algorithm := getU16le m.body 0, transaction := getU16le m.body 2,
           status := getU16le m.body 4 }

/-- True for a successful Open System authentication response (seq 2, status 0). -/
def AuthFrame.isOpenSuccess (a : AuthFrame) : Bool :=
  a.algorithm == 0 && a.transaction == 2 && a.status == 0

namespace Capability
def ess : UInt16 := 0x0001
def privacy : UInt16 := 0x0010
def shortPreamble : UInt16 := 0x0020
def shortSlot : UInt16 := 0x0400
end Capability

/-- Association request for WPA2-PSK-CCMP. -/
def assocRequest (sa bssid : Mac) (ssid : ByteArray) (capability listenInterval seq : UInt16) :
    ByteArray :=
  concat [mgmtHeader MgmtSubtype.assocReq bssid sa bssid seq, u16le capability,
    u16le listenInterval, ie IeId.ssid ssid, ie IeId.supportedRates supportedRates,
    ie IeId.extendedRates extendedRates, wpa2PskCcmpRsnIe]

structure AssocResponse where
  capability : UInt16
  status : UInt16
  aid : UInt16
  deriving BEq, Repr

def parseAssocResponse (frame : ByteArray) : Option AssocResponse := do
  let m ← parseMgmt frame
  if m.fc.subtype != MgmtSubtype.assocResp || m.body.size < 6 then none
  return { capability := getU16le m.body 0, status := getU16le m.body 2,
           aid := getU16le m.body 4 &&& 0x3fff }

/-- Reason code of a deauthentication or disassociation frame. -/
def parseDeauthReason (frame : ByteArray) : Option UInt16 := do
  let m ← parseMgmt frame
  if (m.fc.subtype != MgmtSubtype.deauth && m.fc.subtype != MgmtSubtype.disassoc) ||
      m.body.size < 2 then none
  return getU16le m.body 0

/-! ## Data frames and LLC/SNAP -/

def ethertypeIPv4 : UInt16 := 0x0800
def ethertypeEapol : UInt16 := 0x888E

def llcSnap (ethertype : UInt16) : ByteArray :=
  ByteArray.mk #[0xAA, 0xAA, 0x03, 0x00, 0x00, 0x00] ++ u16be ethertype

/-- Header length of a data frame (A4 when ToDS and FromDS, QoS control for QoS subtypes). -/
def dataHeaderLen (fc : FrameControl) : Nat :=
  24 + (if fc.has Flags.toDS && fc.has Flags.fromDS then 6 else 0)
    + (if fc.subtype &&& 0x08 != 0 then 2 else 0)

/-- Build a non-QoS data frame to the AP (ToDS): A1 = BSSID, A2 = SA, A3 = DA. -/
def dataToAp (bssid sa da : Mac) (seq : UInt16) (ethertype : UInt16) (payload : ByteArray) :
    ByteArray :=
  header3 { ftype := FrameType.data, subtype := DataSubtype.data, flags := Flags.toDS } 0
      bssid sa da seq ++ llcSnap ethertype ++ payload

/-- A parsed data frame (addresses resolved to Ethernet-style DA/SA). -/
structure DataFrame where
  fc : FrameControl
  addr1 : Mac
  addr2 : Mac
  addr3 : Mac
  addr4 : Option Mac
  seqCtl : UInt16
  qos : Option UInt16
  body : ByteArray

def parseData (frame : ByteArray) : Option DataFrame := do
  let fc := FrameControl.decode frame
  if fc.ftype != FrameType.data then none
  let hl := dataHeaderLen fc
  if frame.size < hl then none
  let fourAddr := fc.has Flags.toDS && fc.has Flags.fromDS
  let addr4 := if fourAddr then some (slice frame 24 6) else none
  let qos := if fc.subtype &&& 0x08 != 0 then some (getU16le frame (hl - 2)) else none
  return { fc, addr1 := slice frame 4 6, addr2 := slice frame 10 6, addr3 := slice frame 16 6,
           addr4, seqCtl := getU16le frame 22, qos, body := drop frame hl }

/-- Ethernet-II view of an unprotected (or already decrypted) data frame. -/
structure EthFrame where
  dst : Mac
  src : Mac
  ethertype : UInt16
  payload : ByteArray

/-- Destination/source per the ToDS/FromDS table (802.11-2016 Table 9-26). -/
def DataFrame.dstSrc (d : DataFrame) : Mac × Mac :=
  match d.fc.has Flags.toDS, d.fc.has Flags.fromDS with
  | false, false => (d.addr1, d.addr2)
  | false, true => (d.addr1, d.addr3)
  | true, false => (d.addr3, d.addr2)
  | true, true => (d.addr3, d.addr4.getD d.addr2)

/-- Strip LLC/SNAP from a data frame's body. Rejects protected frames and null data. -/
def toEth (d : DataFrame) : Option EthFrame := do
  if d.fc.has Flags.protectedFrame then none
  if d.fc.subtype &&& 0x04 != 0 then none -- null (no data) subtypes
  if d.body.size < 8 then none
  if !beq (take d.body 6) (ByteArray.mk #[0xAA, 0xAA, 0x03, 0x00, 0x00, 0x00]) then none
  let (dst, src) := d.dstSrc
  return { dst, src, ethertype := getU16be d.body 6, payload := drop d.body 8 }

/-! ## CCMP (802.11-2016 12.5.3) -/

/-- 8-byte CCMP header: PN0 PN1 rsvd (ExtIV | KeyId<<6) PN2 PN3 PN4 PN5. -/
def ccmpHeader (pn : UInt64) (keyId : UInt8) : ByteArray :=
  ByteArray.mk #[pn.toUInt8, (pn >>> 8).toUInt8, 0, (0x20 : UInt8) ||| ((keyId &&& 3) <<< 6),
    (pn >>> 16).toUInt8, (pn >>> 24).toUInt8, (pn >>> 32).toUInt8, (pn >>> 40).toUInt8]

/-- Parse a CCMP header into `(PN, key id)`; requires the ExtIV bit. -/
def parseCcmpHeader (b : ByteArray) : Option (UInt64 × UInt8) :=
  if b.size < 8 || at! b 3 &&& 0x20 == 0 then none else
  let pn := (at! b 0).toUInt64 ||| ((at! b 1).toUInt64 <<< 8) ||| ((at! b 4).toUInt64 <<< 16) |||
    ((at! b 5).toUInt64 <<< 24) ||| ((at! b 6).toUInt64 <<< 32) ||| ((at! b 7).toUInt64 <<< 40)
  some (pn, at! b 3 >>> 6)

/-- Additional authenticated data from a data MPDU header (`hdr` is the MAC header only). -/
def ccmpAad (hdr : ByteArray) : ByteArray :=
  let fc := FrameControl.decode hdr
  let isQos := fc.subtype &&& 0x08 != 0
  -- Subtype bits 4-6 masked; Retry, PwrMgt, MoreData masked; Protected set;
  -- Order masked for QoS data frames.
  let fc0 := at! hdr 0 &&& 0x8f
  let fc1 := ((at! hdr 1 &&& 0xc7) ||| 0x40) &&& (if isQos then 0x7f else 0xff)
  let fourAddr := fc.has Flags.toDS && fc.has Flags.fromDS
  concat [ByteArray.mk #[fc0, fc1], slice hdr 4 18,
    ByteArray.mk #[at! hdr 22 &&& 0x0f, 0],
    if fourAddr then slice hdr 24 6 else ByteArray.empty,
    if isQos then ByteArray.mk #[at! hdr (dataHeaderLen fc - 2) &&& 0x0f, 0] else ByteArray.empty]

/-- 13-byte CCM nonce: priority, A2, PN (big-endian). -/
def ccmpNonce (hdr : ByteArray) (pn : UInt64) : ByteArray :=
  let fc := FrameControl.decode hdr
  let prio : UInt8 :=
    if fc.subtype &&& 0x08 != 0 then at! hdr (dataHeaderLen fc - 2) &&& 0x0f else 0
  concat [ByteArray.mk #[prio], slice hdr 10 6, (u64be pn).extract 2 8]

/-- Encapsulate a plaintext data MPDU (header ‖ body). Sets the Protected bit. -/
def ccmpEncap (tk : ByteArray) (pn : UInt64) (keyId : UInt8) (mpdu : ByteArray) :
    Option ByteArray := do
  let fc := FrameControl.decode mpdu
  if fc.ftype != FrameType.data then none
  let hl := dataHeaderLen fc
  if mpdu.size < hl then none
  let hdr := (take mpdu hl).set! 1 (at! mpdu 1 ||| Flags.protectedFrame)
  let body := drop mpdu hl
  return hdr ++ ccmpHeader pn keyId ++ Aes.ccmEncrypt tk (ccmpNonce hdr pn) (ccmpAad hdr) body

/-- Result of CCMP decapsulation. -/
structure CcmpPlain where
  /-- Header with the Protected bit cleared, followed by the plaintext body. -/
  mpdu : ByteArray
  pn : UInt64
  keyId : UInt8

/-- Verify and decrypt a protected data MPDU. Replay checking (PN strictly
increasing per key/TID) is the caller's job, see `pnAcceptable`. -/
def ccmpDecap (tk : ByteArray) (mpdu : ByteArray) : Option CcmpPlain := do
  let fc := FrameControl.decode mpdu
  if fc.ftype != FrameType.data || !fc.has Flags.protectedFrame then none
  let hl := dataHeaderLen fc
  if mpdu.size < hl + 8 + 8 then none
  let hdr := take mpdu hl
  let (pn, keyId) ← parseCcmpHeader (slice mpdu hl 8)
  let plain ← Aes.ccmDecrypt tk (ccmpNonce hdr pn) (ccmpAad hdr) (drop mpdu (hl + 8))
  return { mpdu := hdr.set! 1 (at! hdr 1 &&& ~~~Flags.protectedFrame) ++ plain, pn, keyId }

/-- Receive replay rule: accept only a PN greater than the last accepted one. -/
def pnAcceptable (last : Option UInt64) (pn : UInt64) : Bool :=
  match last with
  | none => true
  | some l => pn > l

end LeanOS.Wifi.Ieee80211
