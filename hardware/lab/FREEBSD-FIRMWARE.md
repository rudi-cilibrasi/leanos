# FreeBSD EFI firmware replay inputs

`project-freebsd-efi-map.py` converts a captured FreeBSD amd64
`sysctl -b machdep.efi_map` file into the existing hosted corpus's E820-shaped
TSV format. It is an offline, conservative decoder fixture. It does not
reproduce a GRUB handoff, authorize live-memory allocation, or establish
physical platform admission.

The layout comes from FreeBSD 15.0's
[EFI map header](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/x86/include/metadata.h),
[EFI descriptors](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/sys/efi.h),
and [raw loader metadata export](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/amd64/amd64/machdep.c).
The 24-byte header is followed by padding to a 32-byte boundary. The converter
honors the captured descriptor stride, accepts version 1 and types 0–14, and
bounds the complete read to 64 KiB of descriptors. Unknown versions/types,
inconsistent sizes, zero-length ranges, unaligned physical bases and address
overflow are rejected. Uninterpreted padding and descriptor extensions do not
change the projection.

| EFI descriptor | Hosted memory kind |
| --- | --- |
| Conventional memory, type 7 | Usable |
| Unusable memory, type 8 | Bad memory |
| ACPI reclaim, type 9 | ACPI tables |
| ACPI NVS, type 10 | ACPI nonvolatile storage |
| Every other supported type | Reserved |
| Any type with the EFI runtime attribute | Reserved |

In particular, loader and boot-services regions remain reserved. The
conversion assumes no reclamation of those regions after ExitBootServices.
It preserves physical bounds, descriptor order and overlaps; normalization
belongs to the existing Lean decoder. The TSV's end addresses are inclusive.

```sh
python3 hardware/lab/project-freebsd-efi-map.py efi-map.bin memmap.tsv
python3 hardware/lab/test-freebsd-efi-map.py
```

The output path must be new. Retain the original binary, its digest, capture
commands, OS/boot identity, converter revision and the resulting TSV together.
A corpus row using this projection must identify it explicitly rather than
claiming Linux E820 provenance. Both memory-map and ACPI-root replay still
need Lean/generated-C agreement and source-bound negative cases.

For ACPI collection, use the observed `machdep.acpi_root` address and retain
exact RSDP/root/table copies, their physical addresses and checksums. Do not
repair a firmware table. Bound reads to captured ACPI reclaim/NVS regions,
individual table and aggregate limits; compare headers with full reads and
repeat reads. This is a checked sequential live-OS observation, not an atomic
snapshot. Actual legacy GRUB table placement and a reviewed physical copy
path remain separate requirements for issue #331.
