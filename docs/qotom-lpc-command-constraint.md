# Qotom LPC prevents an all-zero Command policy

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

A replacement physical policy must explicitly account for LPC and every other
admitted function. Exempting LPC from the zero check would leave its bus-master
capability outside the proposed deny-all argument. It therefore requires an
independently justified contract for LPC/internal agents, peripheral DMA and
outstanding transactions, plus the serial/recovery requirements. These are
requirements for further work, not conclusions of this audit. Preserve typed
pre-CPL3 rejection until the whole policy is justified; do not reinterpret
synthetic zero-command traces as physical containment evidence.

[datasheet]: https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf#page=1190
