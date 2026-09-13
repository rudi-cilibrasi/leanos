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
`49e0e67d52a914904d1615d3f4ee2da8d11d08b83b1ab7ef2bdadf03ea69d18f`.
The complete serial stream SHA256 is
`f215f86c6a894b2d7b14948cae628485914911657594a8a27bd962a9912ff585`.
The captured Multiboot2 handoff SHA256 is
`c540ca8e9c6d4294d61503ffe33c9f26da3249086ec7d760981e8a7f8f5c6049`.
Within it, the byte-exact E820 tag SHA256 is
`a102ad5b365d12dcadff1a38cbd2f871016e70255537f71897c456d39901e4f7`.
`build-manifest.json` binds every build input and final object audit.
Clean source and prepared revision
`133b441f45a64253d63413c791c69da01cc26892` reproduced that exact ELF.

After the semantic terminal the kernel remained in its absorbing `cli; hlt`
loop. The runner measured 91.73439465794945 seconds of serial quiet, the
external watchdog reset the machine, and FreeBSD boot time changed from
1789324617 to 1789325138. SSH returned and the one-shot request was consumed.
Post-recovery inspection found the expected ELF and GRUB hashes, `request=none`,
and a clean FAT filesystem with 56 MiB free.

Serial used the FTDI FT232R cable `BG03A20M`, a null-modem adapter, and Qotom
COM1 at 38400 baud, 8N1, with no flow control. `capture.sh` records the runner
invocation and `install.sh` records the digest-checked USB update. This is one
bounded physical execution of the named profile; the residual assumptions in
ADR 0019 remain part of the claim.
