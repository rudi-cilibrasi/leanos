# Qotom malformed MADT NMI quarantine capture, 2026-09-12

This protected Win7 Legacy USB boot exercises the Qotom BSP production path
from commit `e66160a092091c89328b8f1f4b703a26e705af0f`. The exact ELF SHA-256 is
`e6b382464cd8f2e2c2803f2f3d25d70e3051ded352bc519c52b1466e3ef82462`.

The native MADT contains four six-byte Local APIC NMI records with invalid
reserved flag bits and LINT values 247, 166, 206 and 39. The production
consumer retained their exact bytes and order, passed them to the generated
scalar policy, and granted no interrupt-routing authority. Memory and the
four-processor topology were published only after that gate returned the
quarantine policy:

```text
LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published topology=published interrupts=masked nmi-routing=quarantined platform-admitted=0
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The terminal-to-recovery quiet interval was 34.310 seconds. GRUB then reported
`DEFAULT request=none` and `CHAIN freebsd disk=hd1`. FreeBSD boot time changed
from 1789208673 to 1789212011, SSH returned, USB serial `11758C40` was unchanged,
and post-recovery inspection found the exact installed ELF and `request=none`.
The raw serial SHA-256 is
`10183577418a5d7c1a884ffbab72bd6afa46b654c294317a8298b6f0912b2659`.

`build-manifest.json` binds the clean committed sources, generated C, page
plans and final ELF. The AP-start audit excludes local-APIC mappings, x2APIC
ICR writes and a retained AP-start path. It records firmware/AP dormancy as an
assumption.

This capture proves recognition and disabled use of these malformed MADT
records at this checkpoint. It does not measure inherited local-APIC LVT
state, mask an independently configured NMI source, establish later interrupt
routing, establish PCI/DMA containment, grant full platform admission, or run
the CPL3 scenario.
