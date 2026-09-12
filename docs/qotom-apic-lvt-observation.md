# Qotom inherited local-APIC LINT observation

The Qotom MADT contains four malformed Local APIC NMI records. The production
boundary recognizes their exact bytes and grants them no routing authority,
but that does not describe the local APIC state inherited from firmware. This
lab image reads LVT LINT0 and LINT1 so a later policy can be based on measured
hardware state rather than on FreeBSD's permissive MADT interpretation.

Build the opt-in image from prepared canonical inputs:

```sh
python3 scripts/build-qotom-recovery-lab.py \
  --prepared-repo . --mode completion --pci-diagnostic --bsp-production \
  --bsp-lvt-observation
python3 scripts/test-qotom-apic-lvt-image.py
```

The observer runs after the production memory/topology checkpoint while
maskable interrupts remain disabled. It rechecks CPUID, executing APIC ID 0,
IA32_APIC_BASE `0xfee00900`, the active root, CR0/CR4/EFER/RFLAGS and the
captured PAT layout. It scans all 4,096 active leaf entries for an existing
`0xfee00000` alias, then borrows the existing ACPI copy aperture. The temporary
leaf is supervisor-only, read-only, NX and PAT-slot-3 UC. Only aligned 32-bit
loads at offsets `0x350` and `0x360` are issued, twice each. The code restores
the exact prior leaf and invalidates both mapping changes before publishing the
four raw values.

The serial record reports the raw first and second samples, whether both pairs
were stable, zero routing authority, zero writes, restored mapping state and
zero platform admission. The capture decoder retains the raw value and decodes
the vector, delivery mode/status, polarity, remote-IRR, trigger and mask bits.
It does not treat any observed value as an accepted interrupt policy.

## Physical result

The protected Qotom capture retained in
`hardware/lab/observations/qotom-apic-lvt-20260912` read both LINT registers as
`0x00010000` twice. Both were masked with fixed delivery mode, vector 0,
active-high edge semantics, idle delivery status and remote-IRR clear. The
observer restored the mapping, issued no APIC writes, granted no routing
authority, and left platform admission false. The watchdog recovery returned
to FreeBSD after 34.318 seconds of quiet serial time.

That result permits a later Qotom policy to require the exact masked inherited
state at its boundary. The observation image itself remains read-only and does
not turn a single boot measurement into a general firmware guarantee.

## Inherited-masked policy image

The separate `--bsp-lvt-policy` image repeats the same bounded read and passes
all eleven observations to the generated
`leanos_qotom_inherited_lvt_policy_query` gate. Lean proves that acceptance is
equivalent to status zero, APIC base `0xfee00900`, executing APIC ID 0, four
`0x00010000` LINT samples, stable reads, zero routing authority, zero writes and
restored mapping state. Errors 90 through 97 identify which boundary failed.

An accepted policy emits `policy=masked-inherited`; rejected or structurally
inconsistent generated output stops before the production record. The policy
does not write an LVT register. It establishes that the exact inherited state
at this checkpoint keeps both firmware LINT inputs masked while IF remains
clear. Firmware, SMM and independent hardware activity remain trusted outside
the bounded transaction.

Build and inspect that image with:

```sh
python3 scripts/build-qotom-recovery-lab.py \
  --prepared-repo . --mode completion --pci-diagnostic --bsp-production \
  --bsp-lvt-policy
python3 scripts/test-qotom-apic-lvt-policy-image.py
```

Firmware, SMM and the other processors remain outside this transaction's
control. Repeated equal reads are a bounded observation, not proof that those
actors cannot change the registers later. A native MMIO fault is terminal and
the watchdog remains the recovery boundary. The final image audit continues to
exclude permanent local-APIC mappings, x2APIC ICR writes and AP-start symbols.
