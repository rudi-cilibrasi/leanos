# Native Qotom copy-root publication capture — 2026-09-12

A protected Win7 Legacy boot completed the admitted Qotom PCI path, built
closed and copy page-table roots, published both roots, and exercised the
bounded copy primitive. The exact final records were:

```text
LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=0 index=16 count=16 commands-accepted=1 assumption-mask=31 admitted=1 contract=qotom-j1900-pci-trust-v1 contract-accepted=1 commands=7,3,3,2,258,2,3,3,3,3,1026,7,3,3,0,3 vtd=not-applicable platform-admitted=1
LEANOS-LAB/1 NO-SMAP-CONTROL profile=qotom-copy-roots-v1 status=0 cr0=2147549215 cr4-before=104 cr4-after=1048680 efer=3328 rflags=6 error-mask=0 strategy=qotom-copy-roots-v1 max-bytes=16 max-aliases=2 reload=mandatory cpl3-authority=0 closed-root-published=0 copy-root-published=0
LEANOS-LAB/1 COPY-ROOTS profile=qotom-copy-roots-v1 status=0 protected=5 removed-aliases=3 retained-present=4088 aliases=2 closed-root=1712128 copy-root=1667072 closed-scan=1 copy-scan=1 transferred=16 bytes-match=1 active-root=1712128 error-mask=0 closed-root-published=1 copy-root-published=1 cpl3-authority=0
LEANOS/3 FINAL status=FAIL reason=qotom-entry-integration-pending
```

The builder protected five linked user text/stack frames. Its closed root
removed three pre-existing aliases and retained 4,088 source mappings. Its
copy root added exactly two supervisor/NX aliases. Full scans accepted both
roots. The audited transfer crossed two source stack pages, moved 16 bytes,
matched the expected bytes, and reloaded the closed root before reporting.
The active CR3 value, 1712128 (`0x1a2000`), therefore matches the closed-root
address; the copy root is 1667072 (`0x197000`).

This run establishes construction and publication of the two roots and a
kernel-mode exercise of the mandatory closed-to-copy-to-closed transition.
It deliberately leaves `cpl3-authority=0`. The next blocker in issue #329 is
to integrate the roots with the production CPL3 entry/return path and prove
that no alternate kernel mapping restores caller access during the copy.

The PCI result remains admission under the initial trust contract. Posted
write drain, continuing TXE-private DMA quiescence, and firmware/SMM
noninterference were assumed rather than measured. VT-d is not applicable to
this J1900 profile.

The raw serial SHA256 is
`17e61f7bb16e324e9dcfce3e6b9d4c4fc6b5df44d9e20feebd638110b0606527`.
The protected ELF SHA256 is
`16ccf8f1e0e62c88b02a2c8b1a8cca75c31a7341fa9bdcbe6aba733d6293e74c`.
The build manifest records clean source revision
`75d666b52ba99817a0f23aa8d79a4c5b3c42769e`, prepared revision
`a8828ef7aae35c016686ba311500dae156c340a3`, and the complete hashed input
set. The final publication-boundary audit SHA256 is
`d56218a87d0eee18d2f1434661ca02112bf30205ef6539de32d1a600527430cd`.

The watchdog recovered FreeBSD after 34.30770358198788 seconds of serial
quiet. Its boot time changed from 1789264229 to 1789264421, and the dated
one-shot request was consumed. Independent SSH inspection confirmed USB
serial `11758C40`, the installed ELF/checksum/GRUB hashes, `request=none`, a
clean FAT filesystem check, no lingering mount, and the recovered Intel TXE
function. Serial used FTDI/null-modem COM1 at 38400 baud, 8N1, with no flow
control.

GRUB reported an 80x25 EGA text framebuffer at physical address `0xb8000`
with pitch 160 and 16 bits per cell. The handoff did not authorize display
output, and no operator monitor observation is included in this evidence.

The first prelaunch attempt used a relative filename in `leanos.sha256`, so
GRUB rejected the checksum file and recovered without launching LeanOS. The
canonical cycle retained here used `/boot/leanos-qotom-lab.elf`; its installed
checksum, GRUB, and ELF hashes were rechecked after recovery.

The previous USB boot tree is preserved on the Qotom as
`/var/tmp/leanos-before-copy-root-75d666b.tar.gz` (SHA256
`0205b6a9cdb90bf8b84ecb2b798fb8afc4773cfee14cc9aac1041dc2ff8f8d7a`).
`install-image.sh` records the guarded installation; `capture.sh` records the
protected runner invocation.
