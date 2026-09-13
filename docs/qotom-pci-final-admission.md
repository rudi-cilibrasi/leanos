# Qotom final PCI observation and admission assumptions

This stage follows every bounded Qotom device transition with a fresh, complete
ECAM enumeration. It binds all sixteen identities, topology fields, and raw PCI
headers through the generated native-header checker, then passes the sixteen
post-transition Command words through a separate generated Lean check:

```text
0007,0003,0003,0002,0102,0002,0003,0003,
0003,0003,0402,0007,0003,0003,0000,0003
```

The order is the native inventory order documented in
[the device-control audit](qotom-native-device-control.md). The vector records
eleven BME clears, SMBus remaining clear, and the fixed host-router and LPC
values. Any scan failure, count change, identity or topology change, or one-bit
Command change is a typed rejection. The helper performs no PCI or MMIO access;
the lab wrapper supplies the fresh snapshot and leaves ECAM read-only.

Command acceptance is only an observation. The generated final admission call
also requires five named inputs, each exactly one:

| Bit | Required statement | Current value | Basis |
| --- | --- | --- | --- |
| 0 | Fixed infrastructure is not an admitted DMA initiator | assumed | Intel 329670-002 section 11.1.2 documents the host transaction-router Command/Status dword as fixed `00000007`; this is an explicit platform assumption, not an observed stop. |
| 1 | LPC performs no DMA | assumed | Section 24.2 states that LPC implements neither bus-master cycles nor DMA. |
| 2 | Posted writes have drained | unestablished | Command readback and clear PCIe Transactions Pending samples do not witness posted-write completion throughout the fabric. |
| 3 | TXE-private DMA is quiescent | unestablished | Section 16.1.1 describes a private multi-context DMA engine controlled by the TXE processor; the host-visible BME clear does not prove it stopped. |
| 4 | Firmware and SMM cannot interfere during the protected interval | unestablished | The current measurements do not exclude later firmware or SMM activity. |

The current lab supplies mask `3`: only bits 0 and 1. It therefore must emit
`status=6`, `commands-accepted=1`, `admitted=0`, and terminate at
`qotom-pci-assumptions`. The exact expected record is:

```text
LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=6 index=16 count=16 commands-accepted=1 assumption-mask=3 admitted=0 commands=7,3,3,2,258,2,3,3,3,3,1026,7,3,3,0,3 vtd=not-applicable platform-admitted=0
LEANOS/3 FINAL status=FAIL reason=qotom-pci-assumptions
```

The [retained physical capture](../hardware/lab/observations/qotom-native-pci-final-20260912)
matches that record. The protected boot recovered FreeBSD automatically and
consumed its one-shot request.

The J1900 profile marks VT-d unavailable because the retained ACPI tables have
no DMAR table and this Bay Trail-D platform does not expose a reviewed remapping
unit. The Qotom path never probes q35 VT-d addresses. `not-applicable` is not a
successful containment result.

Build the complete opt-in diagnostic by adding `--pci-final-admission` to the
Qotom recovery image command. The flag requires `--txe-bme`, which in turn
requires the complete preceding device sequence. Run the generated boundary
test with:

```sh
scripts/check-qotom-pci-final-admission.sh
python3 scripts/test-qotom-pci-final-capture.py
```

The next checkpoint is evidence for posted-write drain, TXE-private DMA
quiescence, and continuing firmware/SMM noninterference. Until all three have a
reviewed witness or an explicitly accepted trust contract, this path must stay
before CPL3 and before production whole-profile dispatch. It does not establish
DMA quarantine and does not close issue #330.
