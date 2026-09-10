# Qotom FreeBSD UEFI firmware capture, 2026-09-10

Read-only capture over pinned SSH from Qotom at 192.168.6.21 running
FreeBSD 15.0-RELEASE-p13. No reboot, USB writes, PCI writes or MSR writes.
This boot reports UEFI. It is not the requested legacy GRUB Multiboot2
handoff and must not be substituted for a physical LeanOS capture.

`capture.py` is the exact local collector, pinned by `capture.json`.
It requires SSHPASS externally, uses passwordless sudo for bounded /dev/mem
reads, and refuses to overwrite its fixed output directory. `commands.json`
retains commands, exit codes, stderr and output hashes. The collector used
assertions and was run with ordinary Python (optimization disabled).

The raw `machdep.efi_map` sysctl has a 32-byte aligned header, 1,440 bytes
of descriptor data, descriptor size 48 and version 1: 30 descriptors.
`efi-map.json` is a decoded projection retaining source order and all defined
fields; no E820 or Multiboot2 conversion has been performed. The raw header
and descriptor padding are uninterpreted bytes. Source contracts reviewed:
FreeBSD releng/15.0 sys/x86/include/metadata.h (header), sys/sys/efi.h
(descriptors), and sys/amd64/amd64/machdep.c (raw loader metadata export).

The RSDP address came from machdep.acpi_root. Every table read was restricted
to one captured ACPI reclaim/NVS region, each read at most 64 KiB and all
physical reads together at most 1 MiB. Both RSDT and XSDT vectors were
followed without rewriting or sorting their bytes. Their distinct table
addresses were collected once each. All SDT checksums passed, all headers
matched full reads, and repeat reads matched byte for byte. EFI metadata and
FreeBSD boot identity also matched before/after capture. This bounds and
checks a sequential live-OS observation; it is not an atomic firmware snapshot.

There are 14 SDTs: RSDT, XSDT and 12 distinct referenced tables. RSDT and
XSDT refer to different FACP versions/addresses; both are retained. The MADT
has enabled APIC IDs 0, 2, 4 and 6. `supplement.json` records exact raw
processor fields and the later same-boot CPUID sample pinned to FreeBSD CPU0,
which reports APIC ID 0. This does not prove dormant APs under LeanOS.

The four raw Local APIC NMI records are retained unchanged. Their LINT bytes
are 247, 166, 206 and 39, matching the unusual values printed by FreeBSD
acpidump. Checksums and repeat reads still match. Their meaning and the
production decoder/runtime treatment need review; do not repair these bytes
to make a topology candidate pass.

The ACPI tables reside near 0xb979b000–0xb97a7418, outside LeanOS's initial
16 MiB identity mapping. The existing `copy_acpi_physical_bytes` path already
provides a temporary supervisor-only NX mapping with a 4 GiB physical limit,
and these captured ranges fit it. Actual legacy table placement and physical
validation of that existing path still need verification. At capture time these inputs had not been replayed. Subsequent hosted replay
uses the explicitly conservative EFI projection documented in
`hardware/lab/FREEBSD-FIRMWARE.md`; it is not a GRUB handoff. No platform,
physical allocator, BSP-only execution or hardware success is claimed.

The repository now retains the conservative projection and exact-table replay
as `firmware-corpus/qotom-j1900-freebsd-uefi`. Its source mode is explicitly
`freebsd-physical`; it does not relabel this capture as Linux E820. The
manifest pins the observed model results and mutations. The actual legacy
GRUB handoff and physical admission work remain outstanding.

`legacy-madt-excerpt.txt` retains the earlier decoded APIC block with all
four LINT values zero and checksum 236. `legacy-comparison.json` records the
original text digest and excerpt transformation. The current raw MADT checksum
is 138. This comparison establishes a difference between observations, not
its cause; boot-mode and firmware-setting changes have not been isolated.
