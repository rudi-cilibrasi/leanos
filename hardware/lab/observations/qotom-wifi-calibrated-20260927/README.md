# LeanOS with full N-PHY calibration — 2026-09-27

LeanOS booted from the SSD image and ran the `connect` program with the
Qotom default `calLevel := 3`: brcmsmac's full `do_nphy_cal` sequence
ported to the Lean DSL — RSSI calibration, precal TX gain, TX IQ/LO
calibration, RX IQ calibration (with RC filter sweep) and save.

```text
WIFI 0470 0x00000000   TX IQ/LO calibration completed
WIFI 0483 0x002903cc   RX IQ coefficients core 0 (b << 16 | a)
WIFI 0483 0x008503f4   RX IQ coefficients core 1
WIFI 0484 0x0000000e   RC filter calibration value
WIFI 0472 0x00000000   RX IQ calibration completed
WIFI 0471 0x00000000   calibration saved
LEANOS-LAB/1 WIFI-DHCP address=192.168.6.30
LEANOS-LAB/1 WIFI-PING listening address=192.168.6.30
```

The RX IQ coefficients agree to within two units with an earlier run of the
same program from the FreeBSD development runner (`0x002a03cb`,
`0x008703f5`, RC value `0x0e`). From the wired workstation, 25/25 pings
were answered with no duplicates, RTT 6.4–23.1 ms (average 9.5 ms).
FreeBSD SSH returned afterwards (boot epoch `1790496718` to `1790498641`).

ELF SHA256 `879ae7170cf83eeb61a697396bba99baeeee5b8c66e85dec6abeebb722782352`
(embeds the network PMK; not retained). Capture SHA256 `d7eabd080bc454eb69ef52967d2eb5cfc2e751ae6ab3835f70890665d7dffdb4`.

Not established: calibration accuracy (no reference measurement), or a
link-quality gain — a three-run A/B from the development runner showed no
measurable difference between no calibration and TX calibration on the
current link.
