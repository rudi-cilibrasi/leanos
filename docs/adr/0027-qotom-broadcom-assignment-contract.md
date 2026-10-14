# ADR 0027: Assigned-Broadcom variant of the Qotom PCI trust contract

- Status: Accepted, issue #559
- Date: 2026-10-13

## Context

[ADR 0018](0018-qotom-pci-initial-trust-contract.md) admits the Qotom J1900
profile under `qotom-j1900-pci-trust-v1`. That contract leaves the Broadcom
BCM43224 at `02:00.0` quarantined in D3hot with Command `0000`. The ring-3
network subject of issue #450 binds a WiFi program for the Broadcom to the
driver subject, so the device must return to D0. Until now a lab-only step
did that outside any reviewed contract. ADR 0018 requires a revision to use
a new profile name and to keep old capture semantics.

## Decision

Add the variant `qotom-j1900-pci-trust-v1-bcm43224-assign-v1`. It extends the
initial contract and changes nothing in it:

1. It applies only after the generated initial contract accepts the retained
   final Command vector and only after the exact successful D3hot record of
   the same boot.
2. It permits one configuration store: the 16-bit PMCSR word of `02:00.0`
   at offset `44`, from `400b` (D3hot) to `4008` (D0), with PME disabled and
   every other field as read.
3. After the PCI PM 1.2 recovery time of 10 ms it requires the complete
   header with Command `0000` and the retained BARs, the unchanged
   capability list, the retained PCIe Device Capability and Control/Status
   (Transactions Pending clear), PMCSR `4008`, and two Transactions
   Pending-clear samples 10 ms apart.
4. It assigns the device only to a program that targets exactly `02:00.0`
   (`14e4:4353`), declares no DMA, writes no configuration dword other than
   the profile's two backplane windows, and can set no Command bit other than
   Memory Space.

The generated exports `leanos_qotom_broadcom_assign_write` and
`leanos_qotom_broadcom_assign_admission`
(`LeanOS/QotomBroadcomAssignment.lean`) decide points 1 to 4. The lab
consumer obtains both results before it binds the program; any mismatch fails
closed at `qotom-broadcom-assign`. Details, sources and tests are in
[the variant notes](../qotom-broadcom-assignment.md).

## Consequences

- The initial contract's premise that every controllable bus master is off
  still holds for the Broadcom: an assignable program can never set Bus
  Master, and the device performs no DMA under it.
- The final-PCI and D3hot records keep their meaning. Old captures are
  unchanged; the variant adds a new `BROADCOM-ASSIGN` record.
- The three trusted premises of ADR 0018 (posted-write drain, TXE-private
  quiescence, firmware/SMM noninterference) are unchanged and unproved.
- The variant does not show that the Broadcom firmware is stopped, that
  configuration reads are faithful, or that the device obeys Command.
- A physical capture is pending. Reviewers should revise the variant under a
  new name if the capture shows a different post-D0 state, or if a later
  program needs DMA or other configuration writes.
