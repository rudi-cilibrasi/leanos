# Native Qotom closed-root CPL3 entry/return capture — 2026-09-12

A protected Win7 Legacy boot completed the admitted Qotom PCI and copy-root
path, entered CPL3 under the subject root twice through the DPL3 `INT 0x80`
gate, completed one return, and terminated at the next named checkpoint. The
exact final records were:

```text
LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=0 index=16 count=16 commands-accepted=1 assumption-mask=31 admitted=1 contract=qotom-j1900-pci-trust-v1 contract-accepted=1 commands=7,3,3,2,258,2,3,3,3,3,1026,7,3,3,0,3 vtd=not-applicable platform-admitted=1
LEANOS-LAB/1 NO-SMAP-CONTROL profile=qotom-copy-roots-v1 status=0 cr0=2147549215 cr4-before=104 cr4-after=1048680 efer=3328 rflags=6 error-mask=0 strategy=qotom-copy-roots-v1 max-bytes=16 max-aliases=2 reload=mandatory cpl3-authority=0 closed-root-published=0 copy-root-published=0
LEANOS-LAB/1 COPY-ROOTS profile=qotom-copy-roots-v1 status=0 protected=5 removed-aliases=3 retained-present=4088 aliases=2 closed-root=1716224 copy-root=1671168 closed-scan=1 copy-scan=1 transferred=16 bytes-match=1 active-root=1716224 error-mask=0 closed-root-published=1 copy-root-published=1 cpl3-authority=0
LEANOS/17 ENTRY-MANIFEST ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS
LEANOS/16 DIRECT-PORT-CONTROL tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS
LEANOS-LAB/1 QOTOM-ENTRY-READY profile=qotom-copy-roots-v1 subject=1 address-space=1 gates=2,6,8,13,14,128 root=closed cpl3-authority=0
LEANOS-LAB/1 QOTOM-ENTRY profile=qotom-copy-roots-v1 status=0 entries=2 returns=1 incoming-root=1523712 closed-root=1716224 active-root=1716224 frame=1 user-if=0 gprs=15 close-readback=1 return-reload=1 error-mask=0 entry-contract=1 cpl3-authority=0
LEANOS/3 FINAL status=FAIL reason=qotom-exception-integration-pending
```

The incoming subject root was 1523712 (`0x174000`), the closed root was
1716224 (`0x1a3000`), and the copy root was 1671168 (`0x198000`). Ordinary
entry saved all fifteen GPRs before scratch use, observed the subject CR3,
reloaded and read back the closed root, and called C only after closure. The
first dispatch returned through the existing audited primitive. User code
verified the returned value and the other fourteen GPRs before entering a
second time. Both frames passed, including disabled user IF and safe control
flags. The second dispatch published the record without granting general CPL3
authority.

This is a bounded synchronous checkpoint. It does not test asynchronous
interrupt routing, physically exercise every terminal exception gate,
authorize arbitrary system calls, implement blocking IPC, or establish a
production dispatcher. The next terminal reason is therefore
`qotom-exception-integration-pending`.

The first IF-enabled attempt reached CPL3 but received an external interrupt
for absent IDT vector 15 at the first instruction, producing a general-
protection frame with error `0x7b`. Keeping user IF disabled allowed both
entries. A subsequent strict-frame attempt showed the second saved RFLAGS as
`0x46`: ZF and PF were set by the probe's last successful comparison while IF
remained clear. The final validator permits arithmetic flags and rejects TF,
IF, DF, IOPL, NT, RF, VM, AC, VIF, VIP, and ID.

The linked audit covers the initial frame operands, all-register-first save,
closed-root reload/readback, the existing return primitive, two user entries,
terminal exception shapes, and ten unsafe mutations. Its SHA256 is
`5fd1fea14cc51f84df34a94c05333715ede1252196eff686e7523bc3555741ce`.
The physical replay strictly checks the entry manifest and direct-port control
records before accepting the entry result.

The raw serial SHA256 is
`50226922d30ea535282dc99390101f722040d6f7bd9ada8a06aea46f0b1c23b0`.
The protected ELF SHA256 is
`53b64275e9d690052cf413c2c1c1431d541d8c9e342a42ee84342503944028b8`.
The build manifest records clean source revision
`295522e51d3a7218598ce562bfb749a29885f254`, prepared revision
`a8828ef7aae35c016686ba311500dae156c340a3`, and the complete hashed input
set.

The watchdog recovered FreeBSD after 34.302511085988954 seconds of serial
quiet. Its boot time changed from 1789277025 to 1789277322, and the dated
one-shot request was consumed. Independent SSH inspection confirmed USB
serial `11758C40`, the installed ELF/checksum/GRUB hashes, `request=none`, a
clean FAT filesystem check, no lingering mount, and the recovered Intel TXE
function. Serial used FTDI/null-modem COM1 at 38400 baud, 8N1, with no flow
control.

GRUB reported an 80x25 EGA text framebuffer at physical address `0xb8000`
with pitch 160 and 16 bits per cell. The handoff did not authorize display
output, and no operator monitor observation is included in this evidence.

The previous USB boot tree is preserved on the Qotom as
`/var/tmp/leanos-before-entry-flags-d0d9e4b.tar.gz` (SHA256
`d584c3ce17637b8b26d4c3913f84fc060559a49e1f037e6b47cb8b4d3ec35ed7`).
`install-image.sh` records the guarded installation; `capture.sh` records the
protected runner invocation.
