# Device-program DMA sinks on the Qotom — 2026-09-29

The LeanOS lab kernel (UEFI boot from the SSD image) ran `scan6` on the
BCM43224 and `kbd` (10 s) on the xHCI as version-3 images whose policies
carry the #448 changes
([ADR 0021](../../../../docs/adr/0021-j1900-device-dma-destinations.md)):

* the WiFi program sets Memory Space and **clears** Bus Master
  (`cfgUpdate32 0x04 0xFFFF0004 0x2`);
* the xHCI policy declares CRCR, DCBAAP, ERSTBA and ERDP as address sinks,
  so `wifi_exec` checked every write to them against the scratch bus range.

```text
LEANOS-LAB/1 WIFI-BEGIN id=0x435314e4 bar0=0xd0700004
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
LEANOS-LAB/1 WIFI-BEGIN id=0x0f358086 bar0=0xd0900004
LEANOS-LAB/1 KBD ready vendor=0x04f2 product=0x0402 type-now
LEANOS-LAB/1 KBD session-end keys=0
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

The keyboard enumerated, so the driver's command ring, device context array,
event ring and ERST were all installed through the checked sink writes, and
none tripped `WIFI_POLICY`. No keys were typed during the 10 s window.

ELF SHA256 `48667a369140f6c4133acbbd88740211cabce4f141dd1966a2550704a38c0206`
(no network secrets). Capture SHA256 `4fe6a58b5854d9afb7be26912c33d24958dfb13973ac5227b7051de99490dceb`.
