import LeanOS.Wifi.Pbkdf2
import LeanOS.Wifi.Aes
import LeanOS.Wifi.Eapol
import LeanOS.Wifi.Ieee80211
import LeanOS.Wifi.Dhcp

/-! Hosted known-answer tests for the pure WiFi protocol layer.

Every expected value is either copied from a published standard/RFC or
computed independently by `tests/wifi-vectors-reference.py` (hashlib/hmac and
the `cryptography` package). Prints one PASS/FAIL line per vector and exits
nonzero on any failure. Nothing here touches hardware or a real network. -/

open LeanOS.Wifi
open LeanOS.Wifi.Bytes (ofHex toHex)

private def hx (s : String) : ByteArray := ofHex s

private def str (s : String) : ByteArray := s.toUTF8

private def range8 (lo hi : Nat) : ByteArray :=
  ByteArray.mk ((List.range (hi - lo)).toArray.map fun i => (lo + i).toUInt8)

structure Ctx where
  failures : IO.Ref Nat

private def check (ctx : Ctx) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"PASS {name}"
  else
    ctx.failures.modify (· + 1)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

private def checkHex (ctx : Ctx) (name : String) (got : ByteArray) (want : String) : IO Unit :=
  let w := hx want
  check ctx name (w.size > 0 && Bytes.beq got w) s!"got {toHex got} want {toHex w}"

/-! ## SHA-1, HMAC, PBKDF2, PMK, PRF -/

private def hashVectors (ctx : Ctx) : IO Unit := do
  -- FIPS 180-2 Appendix A / FIPS 180-4 examples.
  checkHex ctx "sha1 fips180 \"abc\"" (Sha1.hash (str "abc")) "a9993e364706816aba3e25717850c26c9cd0d89d"
  checkHex ctx "sha1 empty" (Sha1.hash ByteArray.empty) "da39a3ee5e6b4b0d3255bfef95601890afd80709"
  checkHex ctx "sha1 fips180 448-bit"
    (Sha1.hash (str "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
    "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
  checkHex ctx "sha1 fips180 one million 'a'" (Sha1.hash (Bytes.replicate 1000000 0x61))
    "34aa973cd4c4daa4f61eeb2bdbad27316534016f"
  -- RFC 2202 section 3.
  let rfc2202 : List (ByteArray × ByteArray × String) := [
    (Bytes.replicate 20 0x0b, str "Hi There", "b617318655057264e28bc0b6fb378c8ef146be00"),
    (str "Jefe", str "what do ya want for nothing?", "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"),
    (Bytes.replicate 20 0xaa, Bytes.replicate 50 0xdd, "125d7342b9ac11cd91a39af48aa17b4f63f175d3"),
    (hx "0102030405060708090a0b0c0d0e0f10111213141516171819", Bytes.replicate 50 0xcd,
      "4c9007f4026250c6bc8414f9bf50c86c2d7235da"),
    (Bytes.replicate 20 0x0c, str "Test With Truncation", "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04"),
    (Bytes.replicate 80 0xaa, str "Test Using Larger Than Block-Size Key - Hash Key First",
      "aa4ae5e15272d00e95705637ce8a3b55ed402112"),
    (Bytes.replicate 80 0xaa,
      str "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data",
      "e8e99d0f45237d786d6bbaa7965c7808bbff1a91")]
  let mut i := 1
  for (k, m, want) in rfc2202 do
    checkHex ctx s!"hmac-sha1 rfc2202 case {i}" (Sha1.hmac k m) want
    i := i + 1
  -- RFC 6070 (the 16777216-iteration case is skipped).
  let rfc6070 : List (String × ByteArray × ByteArray × Nat × Nat × String) := [
    ("c=1", str "password", str "salt", 1, 20, "0c60c80f961f0e71f3a9b524af6012062fe037a6"),
    ("c=2", str "password", str "salt", 2, 20, "ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957"),
    ("c=4096", str "password", str "salt", 4096, 20, "4b007901b765489abead49d926f721d065a429c1"),
    ("c=4096 dkLen=25", str "passwordPASSWORDpassword", str "saltSALTsaltSALTsaltSALTsaltSALTsalt",
      4096, 25, "3d2eec4fe41c849b80c8d83662c0e44a8b291a964cf2f07038"),
    ("c=4096 embedded NUL", hx "7061737300776f7264", hx "7361006c74", 4096, 16,
      "56fa6aa75548099dcc37d7f03425e0c3")]
  for (label, p, s, c, n, want) in rfc6070 do
    checkHex ctx s!"pbkdf2-hmac-sha1 rfc6070 {label}" (Pbkdf2.pbkdf2 p s c n) want
  -- IEEE 802.11-2016 J.4.2 passphrase-to-PSK mapping.
  checkHex ctx "pmk 802.11 J.4 \"password\"/\"IEEE\""
    (Pbkdf2.pmkOfPassphrase (str "password") (str "IEEE"))
    "f42c6fc52df0ebef9ebb4b90b38a5f902e83fe1b135a70e23aed762e9710a12e"
  checkHex ctx "pmk 802.11 J.4 \"ThisIsAPassword\"/\"ThisIsASSID\""
    (Pbkdf2.pmkOfPassphrase (str "ThisIsAPassword") (str "ThisIsASSID"))
    "0dc0d6eb90555ed6419756b9a15ec3e3209b63df707dd508d14581f8982721af"
  checkHex ctx "pmk 802.11 J.4 \"a\"x32/\"Z\"x32"
    (Pbkdf2.pmkOfPassphrase (Bytes.replicate 32 0x61) (Bytes.replicate 32 0x5a))
    "becb93866bb8c3832cb777c2f559807c8c59afcb6eae734885001300a981cc62"
  -- 802.11 PRF-512. Inputs follow the 802.11-2016 J.3 style; expected values are
  -- from the independent Python PRF (the standard text was not consulted byte-for-byte).
  checkHex ctx "prf-512 case 1 (J.3-style inputs, python cross-check)" (Eapol.prf (Bytes.replicate 20 0x0b) "prefix" (str "Hi There") 64)
    "bcd4c650b30b9684951829e0d75f9d54b862175ed9f00606e17d8da35402ffee75df78c3d31e0f889f012120c0862beb67753e7439ae242edb8373698356cf5a"
  checkHex ctx "prf-512 case 2 (J.3-style inputs, python cross-check)"
    (Eapol.prf (str "Jefe") "prefix-2" (str "what do ya want for nothing?") 64)
    "47c4908e30c947521ad20be9053450ecbea23d3aa604b77326d8b3825ff7475c06f51fb9c5313d1e9f90d897d134b72e090fc23150bc8414382043418678e700"
  checkHex ctx "prf-512 case 3 (J.3-style inputs, python cross-check)" (Eapol.prf (Bytes.replicate 20 0xaa) "prefix" (Bytes.replicate 50 0xdd) 64)
    "e1ac546ec4cb636f9976487be5c86be17a0252ca5d8d8df12cfb0473525249ce9dd8d177ead710bc9b590547239107aef7b4abd43d87f0a68f1cbd9e2b6f7607"
  checkHex ctx "prf-512 case 4 (J.3-style inputs, python cross-check)"
    (Eapol.prf (Bytes.replicate 80 0xaa) "prefix-3"
      (str "Test Using Larger Than Block-Size Key - Hash Key First") 64)
    "0ab6c33ccf70d0d736f4b04c8a7373255511abc5073713163bd0b8c9eeb7e1956fa066820a73ddee3f6d3bd407e0682a8b21b58b67358e7a423c3a7b02f154f3"

/-! ## AES, key wrap, CCMP -/

private def aesVectors (ctx : Ctx) : IO Unit := do
  let k := hx "000102030405060708090a0b0c0d0e0f"
  checkHex ctx "aes-128 fips197 C.1 encrypt" (Aes.encrypt k (hx "00112233445566778899aabbccddeeff"))
    "69c4e0d86a7b0430d8cdb78070b4c55a"
  checkHex ctx "aes-128 fips197 C.1 decrypt" (Aes.decrypt k (hx "69c4e0d86a7b0430d8cdb78070b4c55a"))
    "00112233445566778899aabbccddeeff"
  checkHex ctx "rfc3394 4.1 wrap" ((Aes.keyWrap k (hx "00112233445566778899aabbccddeeff")).getD .empty)
    "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5"
  checkHex ctx "rfc3394 4.1 unwrap"
    ((Aes.keyUnwrap k (hx "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5")).getD .empty)
    "00112233445566778899aabbccddeeff"
  check ctx "rfc3394 unwrap rejects corrupted input"
    (Aes.keyUnwrap k (hx "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe4")).isNone

private def ccmpVectors (ctx : Ctx) : IO Unit := do
  -- IEEE 802.11-2016 J.6.4 (M.6.4 in 802.11-2012).
  let tk := hx "c97c1f67ce371185514a8a19f2bdd52f"
  let pn : UInt64 := 0xB5039776E70C
  let hdr := hx "0848c32c0fd2e128a57c5030f1844408abaea5b8fcba8033"
  let plain := hx "f8ba1a55d02f85ae967bb62fb6cda8eb7e78a050"
  let want := "0848c32c0fd2e128a57c5030f1844408abaea5b8fcba80330ce70020769703b5f3d0a2fe9a3dbf2342a643e43246e80c3c04d0197845ce0b16f97623"
  checkHex ctx "ccmp J.6.4 aad" (Ieee80211.ccmpAad hdr) "08400fd2e128a57c5030f1844408abaea5b8fcba0000"
  checkHex ctx "ccmp J.6.4 nonce" (Ieee80211.ccmpNonce hdr pn) "005030f1844408b5039776e70c"
  checkHex ctx "ccmp J.6.4 ccmp header" (Ieee80211.ccmpHeader pn 0) "0ce70020769703b5"
  checkHex ctx "ccmp J.6.4 encapsulated mpdu"
    ((Ieee80211.ccmpEncap tk pn 0 (hdr ++ plain)).getD .empty) want
  match Ieee80211.ccmpDecap tk (hx want) with
  | some p =>
    checkHex ctx "ccmp J.6.4 decapsulate plaintext" (Bytes.drop p.mpdu 24) (toHex plain)
    check ctx "ccmp J.6.4 decapsulate pn/keyid/protected-clear"
      (p.pn == pn && p.keyId == 0 && Bytes.at! p.mpdu 1 == 0x08)
  | none => check ctx "ccmp J.6.4 decapsulate" false "MIC rejected"
  let tampered := (hx want).set! 40 ((Bytes.at! (hx want) 40) ^^^ 1)
  check ctx "ccmp rejects tampered ciphertext" (Ieee80211.ccmpDecap tk tampered).isNone
  -- QoS data frame, TID 5, key id 1 (value from the Python reference).
  let qosMpdu := hx "88093a010200000000010200000000020200000000031000" ++ hx "0500" ++
    hx "aaaa030000000800" ++ range8 0 40
  let qosWant := "88493a01020000000001020000000002020000000003100005000504006003020100f902d87b1e24e89f97753dab11d764e795c99458713a11f7c81ad9c5c8da1f17b3f3b67a62afd1d7c125def35e67cbda073ca88a7c0f55f6"
  checkHex ctx "ccmp qos data (python cross-check)"
    ((Ieee80211.ccmpEncap tk 0x000102030405 1 qosMpdu).getD .empty) qosWant
  match Ieee80211.ccmpDecap tk (hx qosWant) with
  | some p =>
    check ctx "ccmp qos round trip"
      (Bytes.beq (Bytes.drop p.mpdu 26) (Bytes.drop qosMpdu 26) && p.keyId == 1 && p.pn == 0x000102030405)
  | none => check ctx "ccmp qos round trip" false "MIC rejected"
  check ctx "ccmp replay rule" (Ieee80211.pnAcceptable (some 5) 6 && !Ieee80211.pnAcceptable (some 5) 5)

/-! ## 4-way handshake (test-only authenticator) -/

private def rsnIe : ByteArray := Ieee80211.wpa2PskCcmpRsnIe

private def hsVectors (ctx : Ctx) : IO Unit := do
  let pmk := Pbkdf2.pmkOfPassphrase (str "ThisIsAPassword") (str "ThisIsASSID")
  let aa := hx "020000000001"
  let spa := hx "020000000002"
  let anonce := range8 0x10 0x30
  let snonce := range8 0x40 0x60
  let gtk := range8 0xa0 0xb0
  let cfg : Eapol.Config := { pmk, aa, spa, snonce, rsnIe, apRsnIe := some rsnIe }
  -- Authenticator side: independent PTK derivation cross-checked with Python.
  let ptk := Eapol.derivePtk pmk aa spa anonce snonce
  checkHex ctx "4way ptk (python cross-check)" (ptk.kck ++ ptk.kek ++ ptk.tk)
    "2679f4c73eaf26c76d20be254428596e28f8ec0936523fe76eaad91b88561b4f82a2e260af86287dd9cc287ff9fe7230"
  let msg1 : Eapol.KeyFrame :=
    { protocolVersion := 2, keyInfo := 0x008a, keyLength := 16, replayCounter := 1, nonce := anonce,
      keyData := .empty }
  let s0 := Eapol.Supplicant.init cfg
  match s0.handle msg1.encode with
  | .error e => check ctx "4way msg1 accepted" false (repr e).pretty
  | .ok (_, .sendMsg4 ..) | .ok (_, .resendMsg4 _) => check ctx "4way msg1 -> msg2" false "wrong output"
  | .ok (s1, .sendMsg2 m2) =>
    checkHex ctx "4way msg2 bytes (python cross-check)" m2
      "0103007502010a00000000000000000001404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f0000000000000000000000000000000000000000000000000000000000000000a221564c4fddfe48a1ec687154cd1e9b001630140100000fac040100000fac040100000fac020000"
    check ctx "4way msg2 MIC verifies at authenticator" (Eapol.micValid ptk.kck m2)
    let f2 := Eapol.parseKeyFrame m2
    check ctx "4way msg2 carries SNonce and our RSN IE"
      (match f2 with
       | some f => Bytes.beq f.nonce snonce && Bytes.beq f.keyData rsnIe && f.replayCounter == 1
       | none => false)
    let plainKd := Eapol.padKeyData (rsnIe ++ Eapol.gtkKde 1 gtk)
    checkHex ctx "4way msg3 key data padding (python cross-check)" plainKd
      "30140100000fac040100000fac040100000fac020000dd16000fac010100a0a1a2a3a4a5a6a7a8a9aaabacadaeafdd00"
    let wrapped := (Aes.keyWrap ptk.kek plainKd).getD .empty
    checkHex ctx "4way msg3 wrapped key data (python cross-check)" wrapped
      "ac45427ab64882c9d9d1d1d1a882ff208a01f059119e82ab7ce4bf12c8dba478d182ac1aecc21e903c4d090532bbe333d1c793b8612b3d24"
    let msg3 (rc : UInt64) (nonce kd : ByteArray) : Eapol.KeyFrame :=
      ({ protocolVersion := 2, keyInfo := 0x13ca, keyLength := 16, replayCounter := rc, nonce,
         keyData := kd } : Eapol.KeyFrame).sign ptk.kck
    let m3 := (msg3 2 anonce wrapped).encode
    check ctx "4way msg3 before msg1 rejected"
      (match s0.handle m3 with | .error .unexpectedMessage => true | _ => false)
    match s1.handle m3 with
    | .error e => check ctx "4way msg3 accepted" false (repr e).pretty
    | .ok (_, .sendMsg2 _) | .ok (_, .resendMsg4 _) => check ctx "4way msg3 -> msg4" false "wrong output"
    | .ok (s2, .sendMsg4 m4 keys) =>
      checkHex ctx "4way msg4 bytes (python cross-check)" m4
        "0103005f02030a0000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e5c72a4ceac54b5cac28e962cf8ff1590000"
      check ctx "4way msg4 MIC verifies at authenticator" (Eapol.micValid ptk.kck m4)
      check ctx "4way installed TK/GTK/key id"
        (Bytes.beq keys.tk ptk.tk && Bytes.beq keys.gtk.key gtk && keys.gtk.keyId == 1)
      check ctx "4way replayed msg3 rejected"
        (match s2.handle m3 with | .error .replayed => true | _ => false)
      check ctx "4way retransmitted msg3 answered without reinstall"
        (match s2.handle (msg3 3 anonce wrapped).encode with
         | .ok (_, .resendMsg4 m) => Eapol.micValid ptk.kck m
         | _ => false)
    let flipped := m3.set! (m3.size - 1) (Bytes.at! m3 (m3.size - 1) ^^^ 0x01)
    check ctx "4way msg3 with bad MIC rejected"
      (match s1.handle flipped with | .error .badMic => true | _ => false)
    check ctx "4way msg3 with wrong ANonce rejected"
      (match s1.handle (msg3 2 snonce wrapped).encode with | .error .anonceMismatch => true | _ => false)
    let otherIe := hx "30140100000fac020100000fac040100000fac020000"
    let kdOther := (Aes.keyWrap ptk.kek (Eapol.padKeyData (otherIe ++ Eapol.gtkKde 1 gtk))).getD .empty
    check ctx "4way msg3 with mismatched RSN IE rejected"
      (match s1.handle (msg3 2 anonce kdOther).encode with | .error .rsnIeMismatch => true | _ => false)

/-! ## 802.11 frames -/

private def frameVectors (ctx : Ctx) : IO Unit := do
  let mac := hx "020000000002"
  let bssid := hx "0a0b0c0d0e0f"
  checkHex ctx "80211 probe request bytes" (Ieee80211.probeRequest mac (str "QUAIL") 6 7)
    "40000000ffffffffffff020000000002ffffffffffff70000005515541494c010802040b160c12182432043048606c030106"
  checkHex ctx "80211 assoc request bytes"
    (Ieee80211.assocRequest mac bssid (str "QUAIL") 0x0431 10 9)
    "000000000a0b0c0d0e0f0200000000020a0b0c0d0e0f900031040a000005515541494c010802040b160c12182432043048606c30140100000fac040100000fac040100000fac020000"
  checkHex ctx "80211 open auth request bytes" (Ieee80211.authRequest mac bssid 3)
    "b00000000a0b0c0d0e0f0200000000020a0b0c0d0e0f3000000001000000"
  -- Hand-assembled beacon: SSID "QUAIL", rates, DS channel 6, RSN WPA2-PSK CCMP, ext rates.
  let beacon := hx ("80000000ffffffffffff0a0b0c0d0e0f0a0b0c0d0e0f1000" ++
    "0102030405060708" ++ "6400" ++ "1104" ++
    "0005515541494c" ++ "010882848b960c121824" ++ "030106" ++
    "30140100000fac040100000fac040100000fac020c00" ++ "32043048606c")
  match Ieee80211.parseBeacon beacon with
  | none => check ctx "80211 beacon parse" false "parse failed"
  | some b =>
    check ctx "80211 beacon bssid/ssid/channel"
      (Bytes.beq b.bssid bssid && Bytes.beq b.ssid (str "QUAIL") && b.channel == some 6)
    check ctx "80211 beacon interval/capability" (b.beaconInterval == 100 && b.capability == 0x0411)
    check ctx "80211 beacon RSN is WPA2-PSK-CCMP"
      (match b.rsn with
       | some r => r.isWpa2PskCcmp && r.groupCipher == Ieee80211.Suites.ccmp &&
           r.pairwiseCiphers == [Ieee80211.Suites.ccmp] && r.akms == [Ieee80211.Suites.akmPsk] &&
           r.capabilities == 0x000c
       | none => false)
    check ctx "80211 beacon raw RSN IE"
      (match b.rsnIe with
       | some ie => Bytes.beq ie (hx "30140100000fac040100000fac040100000fac020c00")
       | none => false)
  let tkipOnly := hx "0100000fac020100000fac020100000fac020000"
  check ctx "80211 RSN TKIP-only is not WPA2-PSK-CCMP"
    (match Ieee80211.parseRsn tkipOnly with | some r => !r.isWpa2PskCcmp | none => false)
  check ctx "80211 truncated IE rejected" (Ieee80211.parseIes (hx "0005515541")).isNone
  let authResp := hx "b00000000200000000020a0b0c0d0e0f0a0b0c0d0e0f2000000002000000"
  check ctx "80211 auth response parse"
    (match Ieee80211.parseAuth authResp with | some a => a.isOpenSuccess | none => false)
  let assocResp := hx "100000000200000000020a0b0c0d0e0f0a0b0c0d0e0f3000110400000100c0010882848b960c121824"
  check ctx "80211 assoc response parse"
    (match Ieee80211.parseAssocResponse assocResp with
     | some r => r.status == 0 && r.aid == 1 && r.capability == 0x0411
     | none => false)
  checkHex ctx "80211 data frame to AP (EAPOL)"
    (Ieee80211.dataToAp bssid mac bssid 5 Ieee80211.ethertypeEapol (hx "0103005f"))
    "08010000 0a0b0c0d0e0f 020000000002 0a0b0c0d0e0f 5000 aaaa0300 0000888e 0103005f"
  let fromAp := hx "08020000 020000000002 0a0b0c0d0e0f 0a0b0c0d0e10 2000 aaaa030000000800 450000"
  check ctx "80211 data frame from AP to Ethernet view"
    (match (Ieee80211.parseData fromAp).bind Ieee80211.toEth with
     | some e => Bytes.beq e.dst mac && Bytes.beq e.src (hx "0a0b0c0d0e10") &&
         e.ethertype == Ieee80211.ethertypeIPv4 && Bytes.beq e.payload (hx "450000")
     | none => false)

/-! ## DHCP -/

private def bootReply (xid : UInt32) (msgType : UInt8) (mac : ByteArray) : ByteArray :=
  Bytes.concat [hx "02010600", Bytes.u32be xid, hx "00000000", hx "00000000",
    hx "c0a80164", hx "c0a80101", hx "00000000", mac, Bytes.zeros 10, Bytes.zeros 192,
    hx "63825363", ByteArray.mk #[53, 1, msgType], hx "3604c0a80101", hx "330400000e10",
    hx "0104ffffff00", hx "0304c0a80101", hx "06080808080801010101", hx "ff"]

private def dhcpVectors (ctx : Ctx) : IO Unit := do
  let mac := hx "020000000002"
  let xid : UInt32 := 0x12345678
  let (c0, disc) := Dhcp.Client.start mac xid
  checkHex ctx "dhcp discover ip/udp header (python cross-check)" (Bytes.take disc 28)
    "4500014800000000401179a600000000ffffffff0044004301340000"
  checkHex ctx "dhcp discover whole-packet sha1 (python cross-check)" (Sha1.hash disc)
    "2a0295271f2eb57df879329056cf9c21c5b28a25"
  check ctx "dhcp discover ipv4 header checksum verifies"
    (Dhcp.internetChecksum (Bytes.take disc 20) == 0)
  let wrap (p : ByteArray) := Dhcp.ipv4Udp 0xc0a80101 Dhcp.ipBroadcast 67 68 1 p
  let offer := wrap (bootReply xid Dhcp.MsgType.offer mac)
  let (cIgn, outIgn) := c0.handle (wrap (bootReply (xid + 1) Dhcp.MsgType.offer mac))
  check ctx "dhcp offer with wrong xid ignored"
    (outIgn.isNone && match cIgn.state with | .selecting _ => true | _ => false)
  let badSum := offer.set! 10 (Bytes.at! offer 10 ^^^ 0xff)
  check ctx "dhcp packet with bad ip checksum ignored" (c0.handle badSum).2.isNone
  let (c1, req) := c0.handle offer
  check ctx "dhcp offer -> request (requested ip 50, server id 54)"
    (match req.bind Dhcp.parseIpv4Udp |>.bind (fun u => Dhcp.parseMessage u.payload) with
     | some m => m.type? == some Dhcp.MsgType.request && m.xid == xid &&
         m.addrOpt? Dhcp.Opt.requestedIp == some 0xc0a80164 &&
         m.addrOpt? Dhcp.Opt.serverId == some 0xc0a80101
     | none => false)
  let (c2, out2) := c1.handle (wrap (bootReply xid Dhcp.MsgType.ack mac))
  check ctx "dhcp ack -> bound lease"
    (out2.isNone && match c2.lease? with
     | some l => l.address == 0xc0a80164 && l.serverId == 0xc0a80101 &&
         l.subnetMask == some 0xffffff00 && l.router == some 0xc0a80101 &&
         l.dns == [0x08080808, 0x01010101] && l.leaseSeconds == some 3600
     | none => false)
  let (c3, out3) := c1.handle (wrap (bootReply xid Dhcp.MsgType.nak mac))
  check ctx "dhcp nak -> new discover"
    (out3.isSome && match c3.state with | .selecting x => x == xid + 1 | _ => false)

def main : IO UInt32 := do
  let ctx : Ctx := { failures := ← IO.mkRef 0 }
  hashVectors ctx
  aesVectors ctx
  ccmpVectors ctx
  hsVectors ctx
  frameVectors ctx
  dhcpVectors ctx
  let n ← ctx.failures.get
  if n == 0 then
    IO.println "ALL PASS"
    return 0
  else
    IO.println s!"{n} FAILURE(S)"
    return 1
