# Native Qotom no-SMAP control capture — 2026-09-12

A protected Win7 Legacy boot completed the admitted Qotom PCI path and then
measured the processor control state for the bounded copy-root strategy. The
exact final records were:

```text
LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=0 index=16 count=16 commands-accepted=1 assumption-mask=31 admitted=1 contract=qotom-j1900-pci-trust-v1 contract-accepted=1 commands=7,3,3,2,258,2,3,3,3,3,1026,7,3,3,0,3 vtd=not-applicable platform-admitted=1
LEANOS-LAB/1 NO-SMAP-CONTROL profile=qotom-copy-roots-v1 status=0 cr0=2147549215 cr4-before=104 cr4-after=1048680 efer=3328 rflags=6 error-mask=0 strategy=qotom-copy-roots-v1 max-bytes=16 max-aliases=2 reload=mandatory cpl3-authority=0 closed-root-published=0 copy-root-published=0
LEANOS/3 FINAL status=FAIL reason=qotom-copy-roots-pending
```

The native reads establish CR0.WP, EFER.NXE, and disabled interrupts. They
also establish that SMAP, PCID, and PGE were clear. The single audited CR4
write set SMEP and preserved every other observed bit. The generated policy
selected at most 16 copied bytes, at most two aliases, and a mandatory CR3
reload. It did not publish either page-table root and did not authorize CPL3.
The next exact blocker in issue #329 is production construction and
publication of the closed and copy roots.

The PCI result remains admission under the initial trust contract. Posted
write drain, continuing TXE-private DMA quiescence, and firmware/SMM
noninterference were assumed rather than measured. VT-d is not applicable to
this J1900 profile. The capture is therefore evidence for the processor
control transition; it is not physical CPL3 acceptance.

The raw serial SHA256 is
`0561341f1fc67a18e16d9135b64fd380b7450bc12778c6a4b5bab8974966f150`.
The protected ELF SHA256 is
`68cb36fd3e4201c552e1a8debd24f52be51a96eaf182e6814f2eb8c1ec2c0d6d`.
The build manifest records clean source revision
`309586bbe06857f4b304e16a8a440d81c23f74c3`, prepared revision
`332e2fab913cefde2982e5cdff4e2e3c7c4eee8a`, and 166 hashed inputs.

The watchdog recovered FreeBSD after 34.32062935194699 seconds of serial
quiet. Its boot time changed from 1789256815 to 1789260237, and the dated
one-shot request was consumed. Independent SSH inspection confirmed USB
serial `11758C40`, the installed ELF/checksum/GRUB hashes, `request=none`, a
clean FAT filesystem check, no lingering mount, and the recovered Intel TXE
function. Serial used FTDI/null-modem COM1 at 38400 baud, 8N1, with no flow
control.

GRUB reported an 80x25 EGA text framebuffer at physical address `0xb8000`
with pitch 160 and 16 bits per cell. That handoff record does not substitute
for an operator observation of the monitor required by issue #335.

The previous USB boot tree is preserved on the Qotom as
`/var/tmp/leanos-before-nosmap-control-309586b.tar.gz`.
`install-image.sh` records the guarded installation; `capture.sh` records the
protected runner invocation.
