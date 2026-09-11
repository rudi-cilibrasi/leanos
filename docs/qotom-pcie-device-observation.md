# Qotom PCIe Device register observation

The native capability capture identifies PCIe structures on root ports
00:1c.0–3 at offset `0x40`, Realtek endpoints 01:00.0 and 03:00.0 at `0x70`,
and Broadcom 02:00.0 at `0xd0`. Their retained header dwords identify versions
1 or 2 and device/port types, but do not contain Device Capabilities or Device
Status. That missing evidence prevents even determining advertised PCIe FLR
support and the sampled Transactions Pending bit.

`boot/pci-express-observation.h` adds a bounded, read-only callback observer.
It refreshes the complete identity/list against the supplied immutable snapshot,
selects exactly one PCIe structure, reads its Device Capabilities dword at +4
and combined Device Control/Status dword at +8, then refreshes identity/list
again. Only a successful final check publishes the offset and both raw dwords.
A missing structure returns NOT_PRESENT; every non-success has zero payload.

The observer covers versions 1 and 2, endpoint and legacy-endpoint types with
standard type-0 headers, and root ports with type-1 headers. Endpoint slot bits,
FLIT/bit14 extensions, unknown versions/types, duplicate structures, payload
outside 256-byte conventional configuration space and overlapping capability
headers reject. This is an explicit old-device scope, not a claim that newer
PCIe structures are malformed. Lists may contain backward acyclic links.

The conservative access bound is 106 configuration reads: two collections of
at most four identity/list-head checks and 48 headers, plus two payload reads.
Successful nonoverlapping lists have at most 46 headers, so at most 102 reads.
There is no write callback, reset request, polling, allocation or DMA decision.
The caller supplies serialized access, immutable inputs and nonaliasing storage.
Sequential reads and final identity/list agreement do not make an atomic
snapshot or prove payload stability, device quiescence or firmware exclusion.

[Linux's PCI register definitions](https://github.com/torvalds/linux/blob/master/include/uapi/linux/pci_regs.h)
identify PCI_EXP_DEVCAP at +4, FLR support at bit28, PCI_EXP_DEVCTL at +8 and
PCI_EXP_DEVSTA at +10, with Transactions Pending at bit5 of Device Status
(bit21 of the combined dword). The observer preserves both raw dwords without
interpreting either FLR or pending as permission to reset or quarantine.

`tests/pci-express-observation.c` covers all 65,536 capability-flag combinations
for each supported PCI header layout, all aligned locations through `0xfc`,
all 102 read failures in the largest nonoverlapping list, initial and final
list/identity drift, overlapping and duplicate structures, absent and all-ones
payloads, and each payload bit. FLR support and pending values are independent
successful observations. The ordinary and pinned sanitizer runs are included
in `scripts/check-pci-capabilities.sh`.

Native emission, protected decoding and the physical capture are still pending.
This helper supports the remaining device-control work for #330 and #291; it
neither closes those issues nor changes production boot admission.
