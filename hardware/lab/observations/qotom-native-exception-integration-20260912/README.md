# Native Qotom terminal CPL3 invalid-opcode capture — 2026-09-12

A protected Win7 Legacy boot completed the admitted Qotom PCI and copy-root
path, entered CPL3 twice through the DPL3 `INT 0x80` gate, returned from both
ordinary entries, and executed the linked `UD2` checkpoint. The terminal
handler validated the hardware frame and emitted the direct serial marker:

```text
LEANOS-LAB/1 COPY-ROOTS profile=qotom-copy-roots-v1 status=0 protected=5 removed-aliases=3 retained-present=4088 aliases=2 closed-root=1716224 copy-root=1671168 closed-scan=1 copy-scan=1 transferred=16 bytes-match=1 active-root=1716224 error-mask=0 closed-root-published=1 copy-root-published=1 cpl3-authority=0
LEANOS/17 ENTRY-MANIFEST ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS
LEANOS/16 DIRECT-PORT-CONTROL tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS
LEANOS-LAB/1 QOTOM-ENTRY-READY profile=qotom-copy-roots-v1 subject=1 address-space=1 gates=2,6,8,13,14,128 root=closed cpl3-authority=0
LEANOS-LAB/1 QOTOM-ENTRY profile=qotom-copy-roots-v1 status=0 entries=2 returns=1 incoming-root=1523712 closed-root=1716224 active-root=1716224 frame=1 user-if=0 gprs=15 close-readback=1 return-reload=1 error-mask=0 entry-contract=1 cpl3-authority=0
!C6
```

The incoming subject root was 1523712 (`0x174000`), the closed root was
1716224 (`0x1a3000`), and the copy root was 1671168 (`0x198000`). After the
second C dispatch, the existing audited return primitive restored all GPRs and
returned the value `0x6162636465666768`. CPL3 verified that value and then
executed the exact linked `UD2` instruction.

The vector 6 handler observed the subject root on entry, disabled interrupts,
reloaded and read back the published closed root, and validated the exact
fault RIP, user CS/SS, user stack, and fault RFLAGS. In particular, the Qotom
hardware frame sets RF for this fault-class exception. The handler accepted RF
while rejecting TF, IF, DF, IOPL, NT, VM, AC, VIF, VIP, and ID. It then wrote
`!C6` directly to COM1 without calling C and entered an absorbing halt. The
decoder requires that single marker and rejects a structured `FINAL` record.

This is a bounded synchronous exception checkpoint. It does not test timer or
external-interrupt delivery, every terminal gate, production dispatch,
blocking IPC, or `FINAL status=PASS`. The next checkpoint is therefore the
blocking IPC integration tracked by issue #332.

The first physical attempt emitted `!E6`; that diagnostic isolated an
incorrect validator assumption that RF would be clear. The retained successful
capture is from the corrected validator. The linked audit covers both ordinary
and exception variants and rejects eighteen unsafe mutations. Its SHA256 is
`5a4037c7f304f65df7be7bac0830409a08c4d2d39f701abca605577bb9c41e23`.

The raw serial SHA256 is
`5233c0faa708a3bf512def97a6c131dc8cb668105bcb0752fac2cbb4586fdb70`.
The protected ELF SHA256 is
`6092c00a90a3ea96e75cb3b25b2a37f7a6bef63b3ad9515dd20da6a6ee25a8e4`.
The exact-head rebuild produced the same ELF and records clean source revision
`9fcee3b7ed81d4c6402dd49abbe7e930b35b2b84`, prepared revision
`a8828ef7aae35c016686ba311500dae156c340a3`, and the complete hashed input
set.

The watchdog recovered FreeBSD after 91.78076744597638 seconds of serial
quiet. Its boot time changed from 1789280883 to 1789281412, and the one-shot
request was consumed. Independent SSH inspection confirmed USB serial
`11758C40`, the installed ELF/checksum/GRUB hashes, a clean FAT filesystem, no
lingering mount, and the recovered Intel TXE function. Serial used an FTDI
USB-to-DB9 cable and null-modem adapter on COM1 at 38400 baud, 8N1, with no
flow control.

GRUB reported an 80x25 EGA text framebuffer at physical address `0xb8000`
with pitch 160 and 16 bits per cell. The handoff does not authorize display
output, and no operator monitor observation is included in this evidence.

The previous USB boot tree is preserved on the Qotom as
`/var/tmp/leanos-before-rf-4f8014d.tar.gz` (SHA256
`e3bd51c23ab4ac6d095eeb565801c9a2d0982927698420bd3a564e36edaa3ce0`).
`capture.sh` records the protected runner invocation. The runner initially
retained the raw stream and recovery proof after its 90-second generic ceiling
rejected the otherwise complete 91.78-second recovery interval. Replaying the
same immutable events with the exception-specific 100-second ceiling produced
the decoded artifacts in this directory; no second hardware boot was used.
