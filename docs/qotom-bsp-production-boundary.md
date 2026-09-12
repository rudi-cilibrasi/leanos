# Qotom BSP production boundary

The `LEANOS_QOTOM_BSP_PRODUCTION_CANDIDATE` image exercises the production
handoff, firmware-copy, allocation and publication path with the native Qotom
four-processor MADT. It is a bounded checkpoint for issue #331. It stops before
PCI, interrupt-routing or CPL3 admission and therefore does not grant whole
platform authority.

Build and audit it after a canonical image build:

```sh
python3 scripts/build-qotom-recovery-lab.py \
  --prepared-repo . --mode completion --pci-diagnostic --bsp-production
python3 scripts/test-qotom-bsp-production-image.py
```

The ELF is `build/qotom-bsp-production-lab/leanos-qotom-lab.elf`. The builder
accepts the same checkout as its prepared input, while retaining the existing
source and generated-object-graph identity checks. It regenerates the prelink
and final page plan, links the freestanding scalar MADT consumer, verifies
Multiboot2, and records both MSR-write and AP-start audits in the manifest.

## Runtime boundary

The Qotom path keeps interrupts disabled and follows the ordinary production
sequence through these operations:

1. copy the bounded Multiboot2 handoff;
2. replay the generated memory projection and select the advertised RSDT or
   XSDT;
3. copy the selected root and every advertised SDT through the temporary
   supervisor aperture;
4. require complete copies and exactly one valid MADT;
5. sample CPUID and IA32_APIC_BASE again on the executing CPU;
6. consume the actual MADT entry bytes with the allocation-free generated
   Qotom stream;
7. recognize all four exact malformed Local APIC NMI records and require that
   the candidate grants them no interrupt-routing authority;
8. pass the consumer's status, detail, APIC ID, processor count and APIC base
   through the generated root/copy/publication gate; and
9. scrub rejected frames and publish the generated memory and topology result.

The final gate accepts the native profile only with BSP ID 0, four enabled
processors, IA32_APIC_BASE `0xfee00900`, a matching executing ID, one MADT, and
a complete root-copy sequence. It rejects a caller that replaces the consumer
result with the older singleton-shaped count. Ordinary and ASan/UBSan hosted
runs cover mutations of every gate class and execute the exported function.

Successful passage emits:

```text
LEANOS-LAB/1 QOTOM-BSP-PRODUCTION profile=qotom-bsp-v1 memory=published topology=published interrupts=masked nmi-routing=quarantined platform-admitted=0
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The recovery image resets after 30 seconds. Its GRUB one-shot token remains
bound to the ELF SHA-256 and then chains to the configured FreeBSD disk.
After installing the audited ELF and matching GRUB hash, capture it with:

```sh
SSHPASS=... python3 scripts/run-qotom-recovery-lab.py \
  --host freebsd@HOST --host-key-alias freebsd.lan \
  --ssh-prefix "sshpass -e ssh" --usb-serial USB_SERIAL \
  --serial-device /dev/serial/by-id/ADAPTER \
  --elf build/qotom-bsp-production-lab/leanos-qotom-lab.elf \
  --output /path/to/new-capture --scenario watchdog-leanos --bsp-production
```

The classifier requires the digest-bound watchdog load, one boot record, the
exact production and terminal records, at least 30 seconds of serial quiet,
the consumed default request, the FreeBSD chain marker, a changed FreeBSD boot
time and restored SSH.

## Malformed NMI-record policy

[ACPI 6.6 section 5.2.12.7](https://uefi.org/specs/ACPI/6.6/05_ACPI_Software_Programming_Model.html#local-apic-nmi-structure)
limits a Local APIC NMI record to LINT0 or LINT1 and uses the MPS INTI flag
format, whose upper twelve bits must be zero and whose polarity/trigger value
2 is reserved. The native records have LINT values 247, 166, 206 and 39 and
nonzero reserved flag bits. Lean proves that all four are unusable as routes.

The consumer packs the actual six bytes of every type-4 record, preserving
table order, and passes all four values to a generated scalar gate. Acceptance
requires the exact retained sequence and zero routing authority. A missing,
additional, reordered or byte-mutated record fails before topology
publication; a caller that asks to use the records also fails. The production
record says `nmi-routing=quarantined`, so a physical capture cannot silently
attribute topology success to repaired or interpreted firmware bytes.

Quarantine means this checkpoint does not program a local-APIC LVT from the
malformed records and keeps IF clear. The opt-in inherited-LVT policy described
in `docs/qotom-apic-lvt-observation.md` additionally requires both BSP LINT
inputs to remain at the physically measured masked value `0x00010000`, with
stable repeated reads and no APIC write. It grants no later interrupt-delivery
authority; that remains a requirement for the CPL3 profile.

## AP-start exclusion and assumptions

An xAPIC INIT or startup IPI requires a write to the local-APIC ICR page. An
x2APIC IPI uses the x2APIC ICR MSR. The final-object audit reads both generated
CPU page-plan arrays directly from the linked ELF and rejects any present leaf
whose physical frame is `0xfee00000`. It also composes the existing raw-byte
WRMSR audit, which permits exactly the eight reviewed bootstrap normalization
writes and no x2APIC ICR write. A negative fixture inserts each forbidden
mechanism into a copy of the final ELF and requires rejection. The image has no
retained AP-start or trampoline symbol and halts at the checkpoint with IF
clear.

This establishes that the reviewed LeanOS image has no architectural path to
start another processor during this checkpoint. It assumes the other
processors are dormant on entry and remain so unless software sends INIT/SIPI.
Firmware, SMM, external debug agents, reset behavior, hotplug and independent
hardware activity remain trusted. The audit records
`firmware_ap_dormancy_assumed=true` and `ap_dormancy_established=false` so the
artifact cannot be presented as a measurement of the other cores.

## Remaining work

The opt-in boundary now rejects attempts to interpret the malformed NMI records
and rejects inherited BSP LINT state other than the exact measured masked
value. It does not authorize later interrupt delivery. It also does not
establish PCI/DMA quarantine, SMM exclusion, no-SMAP isolation, full platform
admission or CPL3 execution. Those conditions must be composed under issue 291
before a successful platform record can replace `qotom-platform-pending`.
