# Qotom ACPI trial stopped by PCI enumeration

The protected physical trial used clean source
`02d8b59b745b286924414536c8e95591e6d761e1` and image SHA-256
`22d2b53973bfbc7af01b54be683336b1e5fcf20b3b159c44573cee4bda51d4b3`.
The connection was FTDI USB serial through a null modem to COM1,
38400 baud, 8N1, no flow control, with legacy BIOS USB boot.

The actual Multiboot2 handoff was retained. CPU selection returned 65536
and MSR readback returned 1. PCI enumeration hit the 16-function capacity
at bus 168, device 1, function 6 (`a8:01.6`). It discarded partial headers
and emitted `FAIL reason=qotom-pci-enumeration`. This address differs from
prior successful 16-function scans. It is an observed scan failure location,
not proof that a device exists there; its cause remains unresolved.

No ACPI table transport occurred: the ACPI hook follows successful PCI
capture. The result's `acpi: null` must not be interpreted as successful
ACPI capture or as absence of ACPI tables. Platform and CPL3 admission
remain false. The runner successfully classified rejection and recovery.

FreeBSD SSH returned, boot time changed from 1789100610 to 1789102749,
and the one-shot request was consumed. Post-FINAL quiet was 34.320 seconds.
The historical `hang_recovery=true` in result.json labels the protected
scenario; this was not an injected hang and does not prove watchdog expiry.
recovery.json records `hang_recovery=false` for the completed-run recovery.

Original serial bytes, timestamped events, raw handoff, replay inputs, and
recovery records are retained. No partial PCI inventory is reconstructed.
