# Native Qotom ACPI observation before PCI enumeration

Clean source `df395d8d1b36fef3a1be11bbad1eaab141dd14ed` built ELF
`abe29c5e2566db2b7a4adad3360757cf9434f9ae2ab9b194f3827eb4f935a9be`.
The bounded ACPI copier runs after CPU/MSR checks and before the independent
PCI observation. A successful PCI scan never granted memory or DMA admission;
the copier retains its existing bounds, physical aperture, root selection,
checksum and complete-copy checks. Neither observation grants admission.

The actual Multiboot2-selected XSDT at `0xb979f078` and ten referenced tables
were captured, totaling 3,951 SDT bytes. The selected set is XSDT, FACP, APIC,
FPDT, MCFG, LPIT, HPET, three SSDTs, and UEFI. These are full native table
bytes, not FreeBSD reconstructions or directory headers. Internal references
such as DSDT/FACS were not followed. Checksums and root-address binding passed;
full topology/model admission is separate work.

PCI enumeration completed with 16 functions, but the trace observed two CF8
mismatches. The first mismatch selected the same EHCI offset `00:1d.0/0x6c`
as the preceding failed trial. Completion therefore does not establish atomic
inventory provenance or exclusive configuration access. The existing inventory
checker returned count rejection 65536. FINAL remains
`FAIL reason=qotom-platform-pending`, with platform/CPL3 admission false.

The FTDI/null-modem COM1 connection used 38400 baud, 8N1, no flow control.
The legacy USB path passed all five selected boot tests after eight native
QEMU cases passed. The QEMU capacity-rejection case retained its ACPI tables
and matched independent QMP memory. USB file hashes and filesystem were
verified after installation and remount.

FreeBSD SSH returned; boot time changed from 1789104190 to
1789104740; the one-shot request was consumed. Post-FINAL
quiet was 34.321 seconds. The historical result field
`hang_recovery=true` names the protected scenario and does not prove watchdog
expiry; this was not an injected hang test.

Raw serial SHA-256: `e95609e0fb52d1340e5ce98e3f443c48609fd3e50ab928bd8a7213f786722ed5`.
Original serial bytes, event timestamps, raw handoff, full ACPI files, PCI trace,
replay inputs, build provenance, and recovery records are retained unchanged.
