# Qotom inherited-masked local-APIC LVT policy capture, 2026-09-12

This protected Win7 Legacy USB boot exercises the proved inherited-LVT policy
from commit `99385529d8c7ab3d10f7bf0b41dfd1f11d7c5f5c`. The exact ELF SHA-256 is
`e828a7b4e244b8886ad754e7b8465c77029bce29b6c75bea0fa2f332889c10f8`.

The production boundary observed LVT LINT0 and LINT1 twice on executing APIC ID
0. All four reads returned `0x00010000`. The generated scalar gate accepted
that exact masked state with the expected APIC base, stable sampling, zero
routing authority, zero writes and exact restoration of the temporary mapping:

```text
LEANOS-LAB/1 APIC-LVT profile=qotom-lvt-v1 status=0 apic-base=4276095232 executing=0 lint0-first=65536 lint1-first=65536 lint0-second=65536 lint1-second=65536 stable=1 routing-authority=0 writes=0 map-restored=1 platform-admitted=0
LEANOS-LAB/1 APIC-LVT-POLICY profile=qotom-lvt-v1 status=0 detail=0 lint0=65536 lint1=65536 policy=masked-inherited routing-authority=0 writes=0 map-restored=1 platform-admitted=0
LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published topology=published interrupts=masked nmi-routing=quarantined platform-admitted=0
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The linked-image audit shows exactly four calls to the single 32-bit MMIO load,
two mapping invalidations, no MMIO store, no permanent local-APIC mapping, no
x2APIC ICR write, and no retained AP-start path. The policy never programs an
LVT register and keeps IF clear.

The terminal-to-recovery quiet interval was 34.319 seconds. GRUB then reported
`DEFAULT request=none` and `CHAIN freebsd disk=hd1`. FreeBSD boot time changed
from 1789216034 to 1789218071, SSH returned, USB serial `11758C40` was unchanged,
and post-recovery inspection found the exact installed ELF and checksum with
`request=none`. The raw serial SHA-256 is
`28f8feaffdfcd06b2948d12735cb3e5f357a864cb1a19d5bc37b5705d788e739`.

This capture establishes the exact inherited-masked BSP LINT policy at the
production topology checkpoint. Firmware, SMM and independent hardware
activity remain trusted outside the bounded transaction. The result grants no
later interrupt-delivery authority and no whole-platform or CPL3 admission.
