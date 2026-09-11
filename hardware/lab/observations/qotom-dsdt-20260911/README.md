# Native Qotom DSDT capture

Image source 490c0822cb312a8b37da15329513de323a987577, clean build.
ELF SHA256: `d02ea7892b4f31b96372beab8daadbd0b1ca215943d623419a1c58dd501eeadb`.
Host test correction 903217b adds bounded serial time for ACPI captures;
it does not change the image or hardware watchdog. All eight QEMU image cases
passed, with independent QMP memory comparison including the DSDT. The initial
USB test expired during DSDT output at its old 15-second deadline. The complete
23-case suite then passed with the bounded ACPI transmission allowance.

Win7 legacy USB boot; FTDI/null modem COM1, 38400 baud, 8N1, no flow control.
The copied XSDT selects a unique FADT, whose selected DSDT is at 0xb979f180.
The DSDT is 30800 bytes, SHA256
`e02b949e57c1e9eae6714dd67bce15dc25df349167235612f19e8cd2df14543f`.
The capture includes the root, ten ordered root children, and the FADT-linked
DSDT, all validated and copied before publication within the existing budget.
PAT/control observations remain 0x0007040600070406 / CR0 0x8001001f /
CR3 0x150000 / CR4 0x68; executing BSP APIC ID 0, IA32_APIC_BASE 0xfee00900.

`dsdt.dsl` is an offline iasl disassembly of the exact captured DSDT alone;
`dsdt-decompile.log` includes the independently checked input hash and tool
output. It identifies \_SB_.PCI0.PDRC (PNP0C02, UID1), whose BUF0 begins with
Memory32Fixed ReadWrite base 0xe0000000, length 0x10000000. Its serialized
_CRS returns BUF0 unconditionally. This matches the same-boot MCFG range.
The kernel did not execute AML. A reviewed mapping/resource contract still
must consume these bytes; disassembly is not itself runtime admission.

PCI enumeration reported 16 functions after 65776 reads, but the raw trace
records four CF8 selector mismatches. This image predates PR #386's immediate
rejection fix. Thus completion is not authoritative inventory evidence.
FINAL FAIL reason qotom-platform-pending; the fifteen-function inventory
checker rejects with result65536. No quarantine or CPL3 admission is claimed.

Protected recovery passed: 34.311359593004454 seconds quiet after FINAL,
FreeBSD SSH restored, boot time changed from1789131073 to1789132116,
and request=none verified. The USB install log retains filesystem/hash checks;
backup is /var/tmp/leanos-before-ecam-490c082.tar.gz on FreeBSD. Hardware recovery
recipes are unchanged. This is lab reset evidence, not canonical halt evidence.
