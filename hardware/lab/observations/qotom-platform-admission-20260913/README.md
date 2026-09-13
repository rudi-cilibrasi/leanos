# Qotom typed platform-admission capture — 2026-09-13

A protected Win7 Legacy boot admitted the closed
`qotom-j1900-clbtm210-v2` whole-machine profile before entering CPL3. The
serial stream contains the exact gate record immediately before the bounded
blocking-IPC scenario:

```text
LEANOS-LAB/1 PLATFORM-ADMISSION profile=qotom-j1900-clbtm210-v2 version=2 status=PASS cpl3-authority=1 vtd=not-applicable assigned-edu=not-applicable terminal=serial-final-halt
LEANOS-LAB/1 QOTOM-IPC-READY profile=qotom-blocking-ipc-v1 subjects=2 interrupts=masked timer-gate=absent pic=masked copy-in=readonly-root copy-out=writable-root cpl3-authority=1
```

The run then completed eight semantic syscalls, one contained CPL3 page fault,
two context switches, two copy transfers, one block, one wake, and one exact
delivery. It ended at:

```text
LEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1
```

The admitted manifest binds the physical XSDT and 12-table ACPI set, the
19-entry Multiboot2 E820 map, the exact 16-function PCI final vector and trust
contract, COM1 at 38400 8N1, the executing BSP APIC ID 0 within a four-processor
MADT, the no-SMAP copy-root controls, and the fixed two-subject scenario. No AP
startup path was published. `ap-start-audit.json` additionally audits this
exact retained ELF: neither boot plan maps the Local APIC page, no AP-start
symbol is linked, and no x2APIC ICR write exists. VT-d and assigned EDU support
are explicitly not applicable for this profile.

The final ELF SHA256 is
`2ca33caa063698c1648fbc630c27d8c9ccc46031553ef479de881b792b51e9e5`.
The complete serial stream SHA256 is
`45acf984db238993b6e6b085312f70b21e78a7a7c80b44dc2d8a2727d1a2c4c4`.
The captured Multiboot2 handoff SHA256 is
`6a69e75497f2a414f745a23a977a76b2e1885b63ec35e45abe2532b0e8f1a02f`.
`build-manifest.json` binds every build input and final object audit.
Clean source and prepared revision
`c01cdc0a8831ccdbfb53049bbb695a040fd4c5de` reproduced that exact ELF.

After the semantic terminal the kernel remained in its absorbing `cli; hlt`
loop. The runner measured 90.83545916998992 seconds of serial quiet, the
external watchdog reset the machine, and FreeBSD boot time changed from
1789303670 to 1789304216. SSH returned and the one-shot request was consumed.
Post-recovery inspection found the expected ELF and GRUB hashes, `request=none`,
and a clean FAT filesystem with 56 MiB free.

Serial used the FTDI FT232R cable `BG03A20M`, a null-modem adapter, and Qotom
COM1 at 38400 baud, 8N1, with no flow control. `capture.sh` records the runner
invocation and `install.sh` records the digest-checked USB update. This is one
bounded physical execution of the named profile; the residual assumptions in
ADR 0019 remain part of the claim.
