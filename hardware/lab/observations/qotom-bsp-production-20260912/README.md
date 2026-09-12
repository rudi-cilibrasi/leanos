# Qotom BSP production boundary capture, 2026-09-12

This protected Win7 Legacy USB boot exercises the production Multiboot2,
root-selected ACPI-copy, memory-allocation and Qotom BSP topology-publication
path from commit `0888bf2b3860b0e27f29ae399fbaebf5c53f434d`. The exact ELF SHA-256 is
`59ce861d636080199b43e03d045070561a408af746355095bde0390db4e100c9`.

The serial stream contains one digest-bound watchdog load followed by the
J1900 CPU/control acceptance, native 2,680-byte handoff, 19-entry memory map,
allocation/scrub/publication records, and:

```text
LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published topology=published interrupts=masked platform-admitted=0
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The terminal-to-recovery quiet interval was 34.315 seconds. GRUB then reported
`DEFAULT request=none` and `CHAIN freebsd disk=hd1`. FreeBSD boot time changed
from 1789206209 to 1789206552, SSH returned, USB serial `11758C40` was unchanged,
and post-recovery inspection found the exact installed ELF and `request=none`.
The raw serial SHA-256 is
`f30a455cfa6e868074d2658cf8e509e9839537e8d9897641800529a2273e1643`.

`build-manifest.json` binds the committed sources, generated C, page plans and
final ELF. The retained AP-start audit found no local-APIC physical mapping in
either linked CPU page plan and no x2APIC ICR MSR write. It records firmware/AP
dormancy as an assumption, not established evidence.

This capture admits the production memory/topology boundary only. It does not
validate the malformed native local-APIC NMI routes, PCI/DMA containment, SMM
or hotplug behavior, full platform admission, or CPL3 execution.
