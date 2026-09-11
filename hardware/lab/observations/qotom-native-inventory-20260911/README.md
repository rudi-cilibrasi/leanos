# Qotom native inventory boot capture

A physical Win7 Legacy USB boot of the lab image completed the ECAM scan and
executed the generated native inventory checker over its private snapshot:

```text
LEANOS/25 PCI-SCAN codec=1 status=0 count=16 bus=0 device=0 function=0 offset=0
LEANOS-LAB/1 NATIVE-PCI profile=qotom-native-ecam-v1 status=0 index=0 count=16
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The sixteen functions include EHCI at 00:1d.0. Independent generated-array
replay returned one and agreed with the kernel record. The actual protected
runner completed successfully, retaining the raw handoff, all twelve ACPI
tables, bootstrap/memory observations, serial bytes and timestamps. Recovery
returned to FreeBSD SSH after a 34.323018410999794-second post-terminal quiet
interval. Boot time changed from 1789135898 to 1789141779; the one-shot request
was consumed and `request=none` was verified afterward.

ELF SHA256: `7b35e7ae55a28896c78ec6a5e445faae20adcff94f5c4e45b335582c5912980f`.
COM1 used 38400 baud, 8N1, no flow control through the FTDI adapter and null
modem. USB serial was 11758C40. The guarded installer backed up the prior boot
files and verified the filesystem and installed hashes. Recovery configuration
remained intact. The build manifest honestly records source revision 32c958d
with dirty integration files at build time; it is not relabeled as the later
integration commit c8313a3 used by the capture runner.

This is physical inventory comparison evidence, not DMA quarantine or platform
admission. No PCI Command writes were introduced, the host/LPC and USB/TXE
policy obligations remain, and CPL3 was not entered. The ELF itself is identified
by hash; this bundle retains its build manifest and the complete capture.
