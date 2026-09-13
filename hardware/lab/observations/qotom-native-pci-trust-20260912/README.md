# Native Qotom initial PCI trust-contract capture — 2026-09-12

A protected Win7 Legacy boot completed every bounded device transition and a
fresh final ECAM enumeration of all sixteen Qotom functions. It selected the
single generated `qotom-j1900-pci-trust-v1` policy. The exact final record was:

```text
LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=0 index=16 count=16 commands-accepted=1 assumption-mask=31 admitted=1 contract=qotom-j1900-pci-trust-v1 contract-accepted=1 commands=7,3,3,2,258,2,3,3,3,3,1026,7,3,3,0,3 vtd=not-applicable platform-admitted=1
LEANOS/3 FINAL status=FAIL reason=qotom-nosmap-pending
```

This is conditional platform admission. The complete identity, topology, final
Command vector, and ordered host-visible transitions were observed. Posted
write drain, continuing TXE-private DMA quiescence, and firmware/SMM
noninterference were not measured; `pci-final.json` marks all three as assumed
and retains their measured fields as false. VT-d is not applicable to this
J1900 profile. LeanOS did not enter CPL3 and did not execute the q35 VT-d path.
The next exact blocker is the no-SMAP isolation policy in issue #329.

The raw serial SHA256 is
`bb66b7ed54b7e02f40974173dc3b4f9f1fd75ff0c5ab7ec7696a573e374bfa5b`.
The protected ELF SHA256 is
`97e9c6e6be402c4c6eebab63664f7f93074abdbb01f8345f8bc2abe01600bcd9`.
The build manifest records clean source revision
`83f66868c4db02eed0090e12e747e085ce2aa241`, prepared revision
`3acf72c5248cb98aa405a49b0d69730ed4ca3e24`, and 161 hashed inputs.

The watchdog recovered FreeBSD after 34.309926871035714 seconds of serial
quiet. Its boot time changed from 1789254160 to 1789256815, and the dated
one-shot request was consumed. Independent SSH inspection confirmed USB serial
`11758C40`, the installed ELF/checksum/GRUB hashes, `request=none`, a clean FAT
filesystem check, no lingering mount, and the recovered Intel TXE function.
Serial used FTDI/null-modem COM1 at 38400 baud, 8N1, with no flow control.

The previous USB boot tree is preserved on the Qotom as
`/var/tmp/leanos-before-pci-trust-83f6686.tar.gz`. `install-image.sh` records the
guarded installation; `capture.sh` records the protected runner invocation.
