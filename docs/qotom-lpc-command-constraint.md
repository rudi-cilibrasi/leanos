# Qotom fixed Command registers prevent an all-zero policy

The merged observation, transition, and executor components implement a
synthetic fifteen-function Command=0 proposal. They must not be installed as
Qotom's production quarantine policy unchanged.

Intel's J1900 datasheet, document **329670-002**, March 2014, section 24.6.2,
printed pages 1190–1191, documents LPC at 00:1f.0. Its Command bits 2:0 are
read-only ones: bus mastering, memory decode, and I/O decode cannot be disabled
through these bits. This contradicts the proposal's required zero readback.
Source: [Intel-authored datasheet, distributor-hosted copy][datasheet].
The downloaded PDF SHA-256 is
`048182ec5a9faece8c78c0f087420065ff1a17ba1107785164e1f467608c6b39`.
This is the inspected 2014 revision, not a claim to have reviewed later errata.

The repository's hash-validated AHCI capture records Command 0x0007 for
`pci0:0:31:0`. That is consistent with the datasheet, but is a read-only
observation, not a write/readback experiment. No physical write was performed
for this audit.

The hosted executor fixture now models those three bits remaining set after
a successful write callback. It must reject at zero-based step nine, BDF
00:1f.0, offset four, with `PCI_COMMAND_READBACK_NONZERO`, ten successful
writes and 146 reads. No later device is accessed and no complete trace count
is published. The existing generic nonzero-readback cases remain in place.

The host bridge / processor transaction router at 00:00.0 also prevents this
policy. Section 11.1.2, printed page 119, documents its entire Command/Status
dword as read-only, hardwired to `0x00000007`. The retained capture agrees.
Host-only and combined host/LPC behavior fixtures both reject at step three,
BDF 00:00.0, after four writes and 50 reads, before reaching LPC. They check the
exact retained dword, unpublished trace count, and no later access. These are
modeled register behaviors, not physical write experiments.

Section 24.2, printed page 1181, documents that the LPC controller implements
neither bus-master cycles nor DMA. Its fixed BME bit therefore does not itself
establish DMA capability. That statement is specific to LPC; it does not cover
the transaction router, other PCU agents, or outstanding transactions elsewhere.

A replacement physical policy must bind each function's identity to its actual
capabilities and register semantics. The existing q35 contract, which only
requires BME for modeled memory mutation, cannot establish non-mutation for a
function whose BME remains set. LPC needs a separately justified capability
assumption; the host bridge needs its own transaction-routing contract. Neither
is a free-form exemption from containment. Peripheral DMA, outstanding
transactions, firmware activity, and serial/recovery preservation still require
justification. Preserve typed pre-CPL3 rejection until the whole policy is
justified; synthetic zero-command traces do not establish physical containment.

[datasheet]: https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf#page=1190
