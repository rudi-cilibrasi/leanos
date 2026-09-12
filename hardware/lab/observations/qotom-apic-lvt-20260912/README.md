# Qotom inherited local-APIC LVT capture, 2026-09-12

This protected Win7 Legacy USB boot observes the BSP local APIC from commit
`4ae1cc614d1a490fc37c1b2ab853ed36a0c33b8f`. The exact ELF SHA-256 is
`f4c9742b38535870727a28c3bb2aff89ac6428493510873f6d9005732020b024`.

After production memory and topology publication, with maskable interrupts
still disabled, the observer borrowed the existing ACPI copy aperture and read
LVT LINT0 and LINT1 twice. Both samples of both registers were `0x00010000`:
masked, fixed delivery mode, vector 0, idle delivery status, active-high, edge
triggered, and remote-IRR clear. The samples were stable across the bounded
read window.

```text
LEANOS-LAB/1 APIC-LVT profile=qotom-lvt-v1 status=0 apic-base=4276095232 executing=0 lint0-first=65536 lint1-first=65536 lint0-second=65536 lint1-second=65536 stable=1 routing-authority=0 writes=0 map-restored=1 platform-admitted=0
LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published topology=published interrupts=masked nmi-routing=quarantined platform-admitted=0
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The linked-image audit shows exactly four calls to the single 32-bit MMIO load,
two mapping invalidations, no MMIO store, no permanent local-APIC mapping, no
x2APIC ICR write, and no retained AP-start path. Runtime checks bound the read
to executing APIC ID 0 with IA32_APIC_BASE `0xfee00900`, supervisor read-only
NX uncached mapping, unchanged control state, and exact restoration of the
borrowed leaf. The serial record reports zero writes and zero routing authority.

The terminal-to-recovery quiet interval was 34.318 seconds. GRUB then reported
`DEFAULT request=none` and `CHAIN freebsd disk=hd1`. FreeBSD boot time changed
from 1789215873 to 1789216034, SSH returned, and post-recovery inspection found
USB serial `11758C40`, the exact installed ELF and checksum, and
`request=none`. The raw serial SHA-256 is
`9ac5af2ead4e75b7ea4294ccd8bfc6e40ec68de5b5a4a46fddf6ed84f38d3383`.

This capture establishes the inherited BSP LINT state in one bounded boot. It
does not prove firmware, SMM, another processor, or later software cannot alter
that state. It grants no interrupt-routing authority, does not establish an
interrupt-controller policy, and does not grant platform or CPL3 admission.
