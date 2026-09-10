# Qotom PCI headers after power cycle

These are sequential configuration-header reads from FreeBSD, collected after
the operator reported that Qotom was back online. The collector ran on mgnuc and
invoked each retained `pciconf` argument vector through SSH and `sudo -n` on the
target. `commands.json` retains raw-output hashes. `provenance.json` identifies
the collector source and target; the report timestamp is the collector's clock.
FreeBSD's clock was in January 2014 after power cycling.

All 15 previously observed functions remain enumerated. SATA at `00:13.0`
changed from `8086:0f21`, class `01018a` (legacy IDE), to `8086:0f23`, class
`010601` (AHCI). This is a changed observation, not an amendment to the old
capture or permission to accept both identities silently. The reason for the
configuration change has not been established.

The raw header byte is `81` on each of the four `00:1c.*` bridges, and `80` on
`00:1f.0`; `pciconf -l` masks the multifunction bit in its displayed `hdr`.
Bridge primary/secondary/subordinate tuples are `(0,1,1)`, `(0,2,2)`, `(0,3,3)`,
and `(0,4,4)`, in function order. The first three secondary buses contain the
observed Ethernet/WLAN/Ethernet endpoints; FreeBSD enumerated no endpoint on
bus 4. The complete raw headers retain command/status, BAR values, bridge
windows and bridge-control words for later review.

These live-OS observations do not establish complete boot-time enumeration,
quarantine, absence of DMA, IOMMU capabilities, or readiness for CPL3. The next
work for issue #330 must define the reviewed boot inventory and containment assumptions,
reject unknown or changed functions/topology, and bind actual writes/readback
to its generated admission model before any q35-only MMIO operation.
