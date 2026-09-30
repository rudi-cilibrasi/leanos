# Confined device programs on the Qotom — 2026-09-29

The LeanOS lab kernel (UEFI boot from the SSD image) ran two version-3
device-program images, each carrying the confinement policy it was admitted
under (`LeanOS/DeviceProgramConfinement.lean`): `scan6` on the BCM43224 under
`qotomBcm43224Policy` and `kbd` (10 s) on the xHCI under `qotomXhciPolicy`.
The kernel compared each declared policy with its `lab_dev_profiles` entry
before running it, and `wifi_exec` enforced the policy on every configuration
access and `physAddr`.

```text
LEANOS-LAB/1 WIFI-BEGIN id=0x435314e4 bar0=0xd0700004
WIFI 0104 0x00100000        command register before the program: decoding off (UEFI)
WIFI 0110 0x1381a8d8        chip id 43224 through the MMIO window
WIFI 7e48 0x00000000        microcode, PHY init and channel-6 receive pass
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
LEANOS-LAB/1 WIFI-BEGIN id=0x0f358086 bar0=0xd0900004
LEANOS-LAB/1 KBD ready vendor=0x04f2 product=0x0402 type-now
LEANOS-LAB/1 KBD session-end keys=0
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

This establishes that the WiFi driver works with only Memory Space enabled:
it now sets the command register through `cfgUpdate32 0x04 0xFFFF0000 0x2`
and never enables Bus Master (the policy forbids it), where the earlier
driver set Memory Space and Bus Master. The keyboard program, whose policy
admits DMA, enumerated the keyboard as before.

The recovery classifier rejects the device-program records, as for the
earlier WiFi captures; the capture is retained as observed.

ELF SHA256 `49a7f56b667879c5e4238c768f851aaf6a57a89060a4c86f4fc97412104d9c39`
(no network secrets). Capture SHA256
`c543ef8154212e51499c4858dd2313a244b4cb18c5638205eb7679aaa176e0b5`.

Not established: a WPA2 join and ping with the confined `connect` image (the
PSK is not available to this run); that path uses the same bring-up and PIO
transmit, and no DMA engine.
