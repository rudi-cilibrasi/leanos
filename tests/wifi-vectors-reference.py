#!/usr/bin/env python3
"""Independent Python reference for tests/WifiVectors.lean.

Recomputes, with hashlib/hmac and (when installed) the `cryptography`
package, every expected value in the Lean WiFi vector test that is not copied
verbatim from a published standard, and checks the published ones too.
It never touches a real network passphrase.

Run: python3 tests/wifi-vectors-reference.py
"""

import hashlib
import hmac
import struct
import sys

try:
    from cryptography.hazmat.primitives.ciphers.aead import AESCCM
    from cryptography.hazmat.primitives.keywrap import aes_key_unwrap, aes_key_wrap
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
except ImportError:  # pragma: no cover
    sys.exit("python3 'cryptography' package is required for the AES cross-checks")

failures = 0


def check(name, got, want):
    global failures
    if isinstance(got, (bytes, bytearray)):
        got = got.hex()
    ok = got == want
    failures += not ok
    print(f"{'PASS' if ok else 'FAIL'} {name}" + ("" if ok else f": got {got} want {want}"))


def show(name, value):
    print(f"VALUE {name} {value.hex() if isinstance(value, (bytes, bytearray)) else value}")


h = bytes.fromhex

# --- SHA-1 (FIPS 180) ---
check("sha1 abc", hashlib.sha1(b"abc").digest(), "a9993e364706816aba3e25717850c26c9cd0d89d")
check("sha1 empty", hashlib.sha1(b"").digest(), "da39a3ee5e6b4b0d3255bfef95601890afd80709")
check("sha1 448-bit", hashlib.sha1(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq").digest(),
      "84983e441c3bd26ebaae4aa1f95129e5e54670f1")
check("sha1 million a", hashlib.sha1(b"a" * 1000000).digest(), "34aa973cd4c4daa4f61eeb2bdbad27316534016f")

# --- HMAC-SHA1 (RFC 2202) ---
rfc2202 = [
    (b"\x0b" * 20, b"Hi There", "b617318655057264e28bc0b6fb378c8ef146be00"),
    (b"Jefe", b"what do ya want for nothing?", "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"),
    (b"\xaa" * 20, b"\xdd" * 50, "125d7342b9ac11cd91a39af48aa17b4f63f175d3"),
    (h("0102030405060708090a0b0c0d0e0f10111213141516171819"), b"\xcd" * 50,
     "4c9007f4026250c6bc8414f9bf50c86c2d7235da"),
    (b"\x0c" * 20, b"Test With Truncation", "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04"),
    (b"\xaa" * 80, b"Test Using Larger Than Block-Size Key - Hash Key First",
     "aa4ae5e15272d00e95705637ce8a3b55ed402112"),
    (b"\xaa" * 80, b"Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data",
     "e8e99d0f45237d786d6bbaa7965c7808bbff1a91"),
]
for i, (k, m, want) in enumerate(rfc2202, 1):
    check(f"hmac-sha1 rfc2202 case {i}", hmac.new(k, m, hashlib.sha1).digest(), want)

# --- PBKDF2-HMAC-SHA1 (RFC 6070) ---
for pw, salt, c, dk, want in [
    (b"password", b"salt", 1, 20, "0c60c80f961f0e71f3a9b524af6012062fe037a6"),
    (b"password", b"salt", 2, 20, "ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957"),
    (b"password", b"salt", 4096, 20, "4b007901b765489abead49d926f721d065a429c1"),
    (b"passwordPASSWORDpassword", b"saltSALTsaltSALTsaltSALTsaltSALTsalt", 4096, 25,
     "3d2eec4fe41c849b80c8d83662c0e44a8b291a964cf2f07038"),
    (b"pass\0word", b"sa\0lt", 4096, 16, "56fa6aa75548099dcc37d7f03425e0c3"),
]:
    check(f"pbkdf2 rfc6070 c={c} dkLen={dk}", hashlib.pbkdf2_hmac("sha1", pw, salt, c, dk), want)

# --- PSK -> PMK (IEEE 802.11-2016 J.4) ---
for pw, ssid, want in [
    ("password", "IEEE", "f42c6fc52df0ebef9ebb4b90b38a5f902e83fe1b135a70e23aed762e9710a12e"),
    ("ThisIsAPassword", "ThisIsASSID", "0dc0d6eb90555ed6419756b9a15ec3e3209b63df707dd508d14581f8982721af"),
    ("a" * 32, "Z" * 32, "becb93866bb8c3832cb777c2f559807c8c59afcb6eae734885001300a981cc62"),
]:
    check(f"pmk {pw[:8]}/{ssid[:8]}", hashlib.pbkdf2_hmac("sha1", pw.encode(), ssid.encode(), 4096, 32), want)


# --- 802.11 PRF (IEEE 802.11-2016 12.7.1.2; vectors J.3) ---
def prf(key, label, data, nbytes):
    out = b""
    i = 0
    while len(out) < nbytes:
        out += hmac.new(key, label + b"\x00" + data + bytes([i]), hashlib.sha1).digest()
        i += 1
    return out[:nbytes]


prf_cases = [
    (b"\x0b" * 20, b"prefix", b"Hi There"),
    (b"Jefe", b"prefix-2", b"what do ya want for nothing?"),
    (b"\xaa" * 20, b"prefix", b"\xdd" * 50),
    (b"\xaa" * 80, b"prefix-3", b"Test Using Larger Than Block-Size Key - Hash Key First"),
]
for i, (k, a, b) in enumerate(prf_cases, 1):
    show(f"prf512 case {i}", prf(k, a, b, 64))

# --- AES-128 (FIPS-197 C.1) ---
enc = Cipher(algorithms.AES(h("000102030405060708090a0b0c0d0e0f")), modes.ECB()).encryptor()
check("aes128 fips197 c.1", enc.update(h("00112233445566778899aabbccddeeff")), "69c4e0d86a7b0430d8cdb78070b4c55a")

# --- RFC 3394 4.1 ---
kek = h("000102030405060708090a0b0c0d0e0f")
check("rfc3394 4.1 wrap", aes_key_wrap(kek, h("00112233445566778899aabbccddeeff")),
      "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5")
check("rfc3394 4.1 unwrap", aes_key_unwrap(kek, h("1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5")),
      "00112233445566778899aabbccddeeff")


# --- CCMP (IEEE 802.11-2016 J.6.4) with an independent AAD/nonce builder ---
def ccmp_parts(hdr, pn):
    fc0, fc1 = hdr[0], hdr[1]
    qos = (fc0 & 0x80) != 0 and ((fc0 >> 2) & 3) == 2
    four = (fc1 & 3) == 3
    hl = 24 + (6 if four else 0) + (2 if qos else 0)
    aad = bytes([fc0 & 0x8F, ((fc1 & ~0x38) | 0x40) & (0x7F if qos else 0xFF)]) + hdr[4:22]
    aad += bytes([hdr[22] & 0x0F, 0])
    if four:
        aad += hdr[24:30]
    prio = 0
    if qos:
        prio = hdr[hl - 2] & 0x0F
        aad += bytes([prio, 0])
    nonce = bytes([prio]) + hdr[10:16] + pn.to_bytes(6, "big")
    return hl, aad, nonce


def ccmp_encap(tk, pn, keyid, mpdu):
    hl, _, _ = ccmp_parts(mpdu, pn)
    hdr = bytearray(mpdu[:hl])
    hdr[1] |= 0x40
    hdr = bytes(hdr)
    _, aad, nonce = ccmp_parts(hdr, pn)
    p = pn.to_bytes(6, "little")
    ccmp_hdr = bytes([p[0], p[1], 0, 0x20 | (keyid << 6), p[2], p[3], p[4], p[5]])
    return hdr + ccmp_hdr + AESCCM(tk, tag_length=8).encrypt(nonce, mpdu[hl:], aad)


tk = h("c97c1f67ce371185514a8a19f2bdd52f")
hdr = h("0848c32c0fd2e128a57c5030f1844408abaea5b8fcba8033")
plain = h("f8ba1a55d02f85ae967bb62fb6cda8eb7e78a050")
hl, aad, nonce = ccmp_parts(hdr, 0xB5039776E70C)
check("ccmp j.6.4 aad", aad, "08400fd2e128a57c5030f1844408abaea5b8fcba0000")
check("ccmp j.6.4 nonce", nonce, "005030f1844408b5039776e70c")
check("ccmp j.6.4 mpdu", ccmp_encap(tk, 0xB5039776E70C, 0, hdr + plain),
      "0848c32c0fd2e128a57c5030f1844408abaea5b8fcba8033"
      "0ce70020769703b5"
      "f3d0a2fe9a3dbf2342a643e43246e80c3c04d019" "7845ce0b16f97623".replace(" ", ""))

# QoS data frame (subtype 8, TID 5, Retry set) -- Python-computed vector.
qos_hdr = h("8809" "3a01" "020000000001" "020000000002" "020000000003" "1000" "0500")
qos_plain = h("aaaa030000000800") + bytes(range(40))
show("ccmp qos mpdu", ccmp_encap(tk, 0x000102030405, 1, qos_hdr + qos_plain))

# --- 4-way handshake cross-check (synthetic, fixed inputs) ---
pmk = hashlib.pbkdf2_hmac("sha1", b"ThisIsAPassword", b"ThisIsASSID", 4096, 32)
aa = h("020000000001")
spa = h("020000000002")
anonce = bytes(range(0x10, 0x30))
snonce = bytes(range(0x40, 0x60))
ptk = prf(pmk, b"Pairwise key expansion", min(aa, spa) + max(aa, spa) + min(anonce, snonce) + max(anonce, snonce), 48)
kck, kek, tk_hs = ptk[:16], ptk[16:32], ptk[32:48]
show("hs ptk", ptk)
rsn_ie = h("30140100000fac040100000fac040100000fac020000")


def eapol_key(version, key_info, key_len, rc, nonce, rsc, key_data, kck_):
    body = struct.pack(">BHHQ", 2, key_info, key_len, rc) + nonce + bytes(16) + rsc + bytes(8)
    tail = struct.pack(">H", len(key_data)) + key_data
    unsigned = struct.pack(">BBH", version, 3, len(body) + 16 + len(tail)) + body + bytes(16) + tail
    mic = hmac.new(kck_, unsigned, hashlib.sha1).digest()[:16]
    return struct.pack(">BBH", version, 3, len(body) + 16 + len(tail)) + body + mic + tail


show("hs msg2", eapol_key(1, 0x010A, 0, 1, snonce, bytes(8), rsn_ie, kck))
show("hs msg4", eapol_key(1, 0x030A, 0, 2, bytes(32), bytes(8), b"", kck))
gtk = bytes(range(0xA0, 0xB0))
kd = rsn_ie + bytes([0xDD, 22, 0x00, 0x0F, 0xAC, 0x01, 0x01, 0x00]) + gtk
kd += b"\xdd" + bytes((-(len(kd) + 1)) % 8)
show("hs msg3 keydata plain", kd)
show("hs msg3 keydata wrapped", aes_key_wrap(kek, kd))

# --- DHCP DISCOVER (independent struct-based builder) ---
mac = h("020000000002")
xid = 0x12345678


def dhcp_discover(mac, xid):
    bootp = struct.pack(">BBBBIHH", 1, 1, 6, 0, xid, 0, 0x8000) + bytes(16) + mac + bytes(10) + bytes(192)
    bootp += h("63825363") + bytes([53, 1, 1, 61, 7, 1]) + mac + bytes([55, 5, 1, 3, 6, 51, 54, 255])
    bootp += bytes(300 - len(bootp))
    udp = struct.pack(">HHHH", 68, 67, 8 + len(bootp), 0) + bootp
    ip = struct.pack(">BBHHHBBH4s4s", 0x45, 0, 20 + len(udp), 0, 0, 64, 17, 0, bytes(4), b"\xff" * 4)
    s = sum(struct.unpack(">10H", ip))
    while s >> 16:
        s = (s & 0xFFFF) + (s >> 16)
    ip = ip[:10] + struct.pack(">H", ~s & 0xFFFF) + ip[12:]
    return ip + udp


d = dhcp_discover(mac, xid)
show("dhcp discover ip header", d[:28])
show("dhcp discover sha1", hashlib.sha1(d).digest())

# --- 802.11 management frames ---
probe = (h("4000" "0000") + b"\xff" * 6 + mac + b"\xff" * 6 + struct.pack("<H", 7 << 4) +
         bytes([0, 5]) + b"QUAIL" + bytes([1, 8, 2, 4, 11, 22, 12, 18, 24, 36]) +
         bytes([50, 4, 48, 72, 96, 108]) + bytes([3, 1, 6]))
show("probe request", probe)
bssid = h("0a0b0c0d0e0f")
assoc = (h("0000" "0000") + bssid + mac + bssid + struct.pack("<H", 9 << 4) +
         struct.pack("<HH", 0x0431, 10) + bytes([0, 5]) + b"QUAIL" +
         bytes([1, 8, 2, 4, 11, 22, 12, 18, 24, 36]) + bytes([50, 4, 48, 72, 96, 108]) + rsn_ie)
show("assoc request", assoc)

print(f"{'ALL PASS' if failures == 0 else f'{failures} FAILURE(S)'}")
sys.exit(1 if failures else 0)
