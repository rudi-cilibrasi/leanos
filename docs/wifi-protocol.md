# WiFi protocol layer (WPA2-PSK / CCMP)

This is the pure protocol and crypto layer for a future LeanOS WiFi station
driver. The first target is a Broadcom BCM43224 (softMAC) joining a WPA2-PSK
(CCMP) network. It covers everything above the radio: key derivation, the
4-way handshake, 802.11 management and data frame codecs, CCMP, and a minimal
DHCP client. The library does no IO. Randomness (SNonce, DHCP xid) and time
(retries, lease expiry) come from the caller.

## Modules

| Module | Contents |
| --- | --- |
| `LeanOS/Wifi/Bytes.lean` | `ByteArray` helpers: BE/LE get/put of 16/32/64-bit values, slicing, XOR, concat, compare, hex |
| `LeanOS/Wifi/Sha1.lean` | SHA-1 (FIPS 180-4) and HMAC-SHA1 (RFC 2104), with precomputed HMAC pad states |
| `LeanOS/Wifi/Pbkdf2.lean` | PBKDF2-HMAC-SHA1; `pmkOfPassphrase` = PBKDF2(passphrase, SSID, 4096, 32) |
| `LeanOS/Wifi/Aes.lean` | AES-128 encrypt/decrypt (S-box derived from its GF(2^8) definition), RFC 3394 key wrap/unwrap, AES-CCM with M=8, L=2 |
| `LeanOS/Wifi/Eapol.lean` | 802.11 PRF, PTK derivation (PRF-384 → KCK/KEK/TK), EAPOL-Key codec (descriptor type 2), HMAC-SHA1-128 MIC, key-data KDE parsing, and the supplicant 4-way handshake state machine |
| `LeanOS/Wifi/Ieee80211.lean` | Frame control, management header, IEs, RSN element parse/build, probe request, beacon/probe-response parse, open auth, association request/response, deauth reason, data frames with LLC/SNAP, CCMP header/AAD/nonce and MPDU encapsulation/decapsulation (non-QoS and QoS data), PN replay rule |
| `LeanOS/Wifi/Dhcp.lean` | IPv4/UDP build/parse (header checksum verified), DHCPDISCOVER/REQUEST, OFFER/ACK/NAK parse, and a client state machine (selecting → requesting → bound) |

The supplicant (`Eapol.Supplicant.handle`) takes message 1 and sends back
message 2, which carries our RSN IE. It takes message 3 and checks it before
sending message 4 and handing over the keys to install. Message 3 checks, in
order:

1. The replay counter is larger than the local one.
2. The MIC verifies.
3. The ANonce matches message 1.
4. The key data unwraps with the KEK.
5. The RSN IE matches the beacon's, when one was configured.
6. A GTK KDE is present.

A message 3 retransmitted after completion gets message 4 again but does not
reinstall the keys. This avoids the nonce reset exploited by key-reinstallation
attacks.

## Running the vectors

```sh
lake build leanos-wifi-vectors && .lake/build/bin/leanos-wifi-vectors
python3 tests/wifi-vectors-reference.py   # independent reference; needs `cryptography`
```

`leanos-wifi-vectors` prints one `PASS`/`FAIL` line per vector and exits
nonzero on any failure. It runs in well under a second. `scripts/check.sh`
runs it too.

To check the PMK of a real network against `wpa_passphrase`, run the
following. The passphrase is only ever read from the environment. Do not put
it in files or scripts.

```sh
lake build leanos-wifi-pmk
LEANOS_WIFI_SSID=<ssid> LEANOS_WIFI_PSK=<passphrase> .lake/build/bin/leanos-wifi-pmk
wpa_passphrase <ssid> <passphrase>
```

## Vectors and their sources

| Area | Vectors | Source of expected values |
| --- | --- | --- |
| SHA-1 | `"abc"`, empty, the 448-bit message, one million `a` | FIPS 180 examples; re-checked with Python `hashlib` |
| HMAC-SHA1 | cases 1–7 | RFC 2202; re-checked with Python `hmac` |
| PBKDF2 | c=1, 2, 4096, the 25-byte and NUL cases (16777216 skipped) | RFC 6070; re-checked with `hashlib.pbkdf2_hmac` |
| PSK → PMK | `password`/`IEEE`, `ThisIsAPassword`/`ThisIsASSID`, `a`×32/`Z`×32 | IEEE 802.11-2016 J.4; re-checked with `hashlib` |
| PRF-512 | four cases with J.3-style inputs | **Python only.** Computed with an independent Python PRF. The leading bytes of cases 1–3 agree with the published J.3 values as remembered, but the standard's text was not available here for a byte-for-byte check |
| AES-128 | FIPS-197 C.1 encrypt and decrypt | FIPS-197; re-checked with `cryptography` |
| Key wrap | RFC 3394 4.1 (128-bit KEK, 128-bit key), plus a corrupted-input rejection | RFC 3394; re-checked with `cryptography` |
| CCMP | IEEE 802.11-2016 J.6.4 (M.6.4 in 802.11-2012): AAD, nonce, CCMP header, full encrypted MPDU, decapsulation, tamper rejection | Standard vector; re-checked with `cryptography` AESCCM using an independent Python AAD/nonce builder |
| CCMP QoS | QoS data frame, TID 5, key id 1 | **Python only** (`cryptography` AESCCM with an independent AAD/nonce builder) |
| 4-way handshake | PTK, exact msg2 and msg4 bytes, msg3 key-data padding and wrapped key data, MIC checks, GTK/key id install, and rejection of replayed messages, bad MICs, wrong ANonce, RSN IE mismatch and message 3 before message 1 | Synthetic. The test file contains a small authenticator. The byte values were cross-checked with an independent Python implementation (`hmac`/`hashlib`/`cryptography`) |
| 802.11 frames | Exact probe request and association request bytes, auth request, parse of a hand-assembled beacon (SSID `QUAIL`, channel 6, RSN WPA2-PSK-CCMP), auth/assoc response, data frames with LLC/SNAP | Hand-assembled. The probe and association requests were also rebuilt with Python `struct` |
| DHCP | DISCOVER IPv4/UDP header and whole-packet SHA-1, header checksum, hand-built OFFER/ACK/NAK through the state machine | Python `struct` rebuild of the DISCOVER, and hand-built replies |

`tests/wifi-vectors-reference.py` recomputes every value that did not come
from a standard. It also checks the published ones.

## What is NOT established

- **No hardware.** Nothing here has driven a BCM43224 or any radio, or talked
  to a real access point. Frame layouts match hand-written and Python-built
  bytes, but they have not been observed over the air.
- **No proofs.** There are no theorems about these modules. The evidence is
  known-answer tests and cross-checks against an independent implementation,
  run on the build host only.
- **Hosted only.** The modules are pure Lean. They have only been compiled and
  run as hosted executables, not in the LeanOS kernel environment.
- **Not implemented:**
  - Group-key (GTK rekey) handshake, TKIP, WPA1, PMF/802.11w, SAE/WPA3, and
    802.1X/EAP.
  - A-MSDU, fragmentation and reassembly, HT/VHT IEs, and power save.
  - DHCP renew/rebind/release, and ARP.
- **No side-channel hardening.** AES and the MIC comparisons are simple byte
  code. They are not constant-time with respect to cache or timing behaviour.
  `Bytes.ctEq` only avoids exiting early.
- **Caller responsibilities.** The caller must supply SNonce and xid
  randomness, retransmit timers, and per-TID receive PN tracking. For PN
  tracking, `pnAcceptable` gives the rule but no state.
