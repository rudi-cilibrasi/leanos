# LeanOS joins the QUAIL WiFi network — 2026-09-26

The LeanOS lab kernel, booted from the Qotom USB stick under the
watchdog-protected one-shot request, ran the Lean-authored BCM43224 driver
program `connect` and joined the local WPA2-PSK network `QUAIL`:

1. Card bring-up, microcode 610.812, N-PHY/radio 2056 initialisation on
   channel 6, MAC and TX setup (brcmsmac port, ISC).
2. Open-system authentication and association with BSSID
   `c4:f1:74:13:8a:47` (association ID 2).
3. WPA2-PSK 4-way handshake: message 1 → message 2, message 3 (MIC verified,
   GTK key id 1 unwrapped) → message 4; two retransmitted message 3s were
   answered with fresh message 4s.
4. DHCP over software CCMP: DISCOVER, OFFER of 192.168.6.30, REQUEST, ACK.
   Lease: address 192.168.6.30, router 192.168.6.1, netmask 255.255.255.0,
   lease time 172800 s (`WIFI 0e05/0e07/0e08/0e09`, network byte order).

The run ended `WIFI-END status=0`, then the unchanged terminal
`FINAL status=FAIL reason=qotom-platform-pending`; the request was consumed
and FreeBSD SSH returned (boot epoch `1790490271` to `1790490625`).

Everything above the executor is Lean: device programs written in the
`LeanOS/Wifi` DSL, including the handshake crypto (SHA-1/HMAC PRF, EAPOL MIC,
AES key unwrap) and CCMP, which are checked in the hosted simulator against
the reference Lean protocol library and against the C executor. The kernel
runs them with the runtime-free executor `hardware/wifi/wifi-exec.h` via
`scripts/build-qotom-recovery-lab.py --wifi-program`; transmit and receive
use the MAC's programmed-I/O FIFOs (no DMA).

ELF SHA256
`4c82b4f1e9f461b7547523a6b64aafb5dc048b862e2c90736bdce2a63bc9ef15`. The
program image embeds the network's PMK and is deliberately not retained; it
is regenerated with `LEANOS_WIFI_DHCP=1 LEANOS_WIFI_PSK=... lake exe
leanos-wifi-gen connect build/wifi/connect.bin build/wifi/fw`.

`cycle-1/serial-redacted.txt` is the COM1 capture (38400 8N1) with the
diagnostic dumps of decrypted network payloads (`WIFI 0e24`, `WIFI 0e26`
lines) removed, since they contain other devices' LAN traffic; its SHA256 is
`4334a452a2d96fb09ba75df28044f3e636647042b120099cb8d84f445dc3baf5`. The unredacted capture had SHA256 `a0808db30f0f369c70315482d0f4bcfd2fa2cb57b018bf36d9c5425ec1f95954` and is not retained.

Not established: sending or receiving application traffic beyond DHCP, ARP,
rekeying, roaming, calibration quality, power-save, or any security property
of the implementation (the SNonce comes from timer jitter; lab grade only).
