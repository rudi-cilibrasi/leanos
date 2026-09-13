# ADR 0018: Initial Qotom PCI trust contract

## Status

Accepted for the opt-in Qotom J1900 hardware profile.

## Decision

Permit the first bounded Qotom CPL3 experiment to proceed without VT-d only
after the complete native device-control sequence and final sixteen-function
PCI rescan pass. Admission selects one generated profile,
`qotom-j1900-pci-trust-v1`. It fixes five premises together; runtime callers
cannot assert independent exemption bits or substitute a different inventory.

The first two premises have public hardware-document support: the host
transaction router has a fixed Command value, and the LPC interface implements
neither bus-master cycles nor DMA. The following three are trusted platform
premises rather than measurements:

1. every posted transaction issued before the final rescan has reached its
   destination;
2. the TXE private DMA engine is quiescent and remains so; and
3. firmware and SMM neither touch LeanOS subject, kernel, page-table, evidence,
   or copy-window frames nor restore device authority during the experiment.

These premises begin after every typed device transition has succeeded and the
generated final identity and Command checks accept the fresh rescan. They end
when LeanOS reaches a terminal state or the protected watchdog resets the
machine. The existing single-BSP firmware/AP premise continues to apply.

The generated `leanos_qotom_pci_initial_trust_contract` export contains this
policy decision. It accepts only the exact final Command vector and internally
supplies all five premises to the conditional admission definition. The lab C
consumer must obtain both the ordinary generated admission result and the named
contract result before reporting `platform-admitted=1`. The normal final-PCI
observation build still supplies only the two documented premises and rejects.

## Evidence interpretation

A physical capture can establish that the complete ordered transition ran,
that every final identity and Command word matched, that q35 VT-d MMIO was not
used, and that the named contract was selected. It cannot observe posted-write
completion across the fabric, TXE-private state, or absence of SMM. Capture
metadata therefore records those three facts as `*_assumed=true` while keeping
the corresponding measured fields false.

Under this contract, `platform-admitted=1` means the bounded Qotom PCI boundary
is accepted conditional on all listed premises. It is not an IOMMU result, a
general J1900 claim, evidence for another firmware revision, or proof of those
premises. VT-d and assigned-device scenarios remain explicitly not applicable.

The legacy COM1 serial path remains available throughout the transition. The
integrated graphics path keeps memory and I/O decode enabled after its ring-idle
check while clearing BME. The boot USB controller paths are stopped, handed off
from firmware, stripped of SMI enables, and have BME cleared; recovery uses a
machine reset before FreeBSD needs them again. These are properties of the
named ordered profile and do not widen the trust premises.

## Rejection and review

Any scan error, inventory or topology change, Command mismatch, earlier typed
device failure, missing generated export, or contract mismatch rejects before
CPL3. The trust-contract build is an explicit opt-in flag and the ordinary
Qotom observation remains fail closed.

Reviewers should reject or revise this profile if a stronger public TXE stop
protocol, a fabric-drain witness, a DMAR-capable replacement platform, or
evidence of firmware interference becomes available. A revision must use a new
profile name and preserve old capture semantics.
