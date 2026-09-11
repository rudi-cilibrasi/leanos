# Qotom xHCI observation before ownership and shutdown

The retained native inventory binds xHCI to index 3, BDF `00:14.0`, identity
`8086:0f35`, class/revision `0x0c03300e`, Command/Status `0x02900006`, and BAR
pair `0xd0900004`, `0`. The memory base is `0xd0900000`; bit 2 describes the
64-bit BAR, so the upper DWORD is part of binding. Recovered FreeBSD topology
places the boot USB stick under xHCI, making protected recovery validation
necessary for any later ownership or stop changes.

Intel document 329670-002 section 14.6.11 describes the 64-bit BAR and 64-KiB
allocation; section 14.7 table 120 lists the capability registers. The reviewed
[Intel-authored datasheet copy](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf)
has SHA256 `048182ec5a9faece8c78c0f087420065ff1a17ba1107785164e1f467608c6b39`.
Linux's [xHCI register declarations](https://github.com/torvalds/linux/blob/master/drivers/usb/host/xhci.h)
also distinguish the seven xHCI 1.0 capability DWORDs from operational registers.
Do not reuse EHCI's configuration-space legacy-list interpretation for xHCI.

`boot/qotom-xhci-capabilities.h` brackets seven DWORD reads at BAR offsets
`0..0x18` with six PCI binding reads: identity, memory decode, class/revision,
header type, and both BAR halves. It requires the chipset's xHCI 1.0/CAPLENGTH
value `0x01000080`, rejects failed or all-ones reads, and retains the remaining
raw parameter/offset words without following them. At most 19 reads occur;
any failure publishes zero fields. The source-derived parameter defaults in
hosted fixtures are synthetic, not a physical capability capture.

This collector grants no mapping authority. Native integration must establish
UC mapping, exclude aliases across the relevant resource, bind the firmware/root,
and restore the private aperture. Callbacks must be bounded and serialized with
immutable, nonaliasing input/output views. Bracketed refresh is not atomicity or
continuing firmware/AP exclusion. No ownership request, stop, reset, BME write,
DMA containment or platform admission is implemented here.

## Separate capability read mapping

`hardware/lab/qotom-xhci-window.h` admits only aligned DWORD addresses
`0xd0900000..0xd0900018`. Each transaction maps the first resource page UC,
read-only, supervisor-only and NX, performs a trusted load into a private sample,
then restores and invalidates the original leaf before publishing. Control or
mapping interference terminates after restoration. A failed load publishes no
value; the gate does not authorize operational or extended-capability accesses.

`qotom-xhci-arm.h` binds both BAR DWORDs and the exact captured controller header
to the firmware/root checks. It rejects present mappings into any page of the
64-KiB xHCI resource, in addition to the existing ECAM alias checks. Failed rearm
clears all authority and arming itself performs no device access. Tests cover
all in-page offsets, upper-BAR bit changes, all 4096 leaf positions for first-page
and ECAM aliases, every resource page, failed loads, restoration and terminal
interference. Native integration is described below; the physical capture is retained below.

## Native capture integration

The builder's `--xhci-capabilities` requires `--ehci-bme` and creates
`build/qotom-xhci-lab`. Native code invokes the collector on the immutable
inventory's index 3 after successful EHCI BME handling. The new reader and
existing ECAM reader share the restored private aperture sequentially. All
contexts are disabled before `XHCI-CAPS`, containing status and seven raw DWORDs.
Local arm rejection uses status 8; collector failure stops at
qotom-xhci-capabilities, and success remains qotom-platform-pending.

The protected runner fingerprints the matching decoder, retains
`xhci-capabilities.json`, and preserves the actual terminal after earlier replay
projections. Decoding requires the complete successful EHCI BME prefix, the
captured xHCI header/BAR pair, exact record order and scalar count, and zero
publication on failure. Synthetic parameter words test framing, not physical
controller values. The built image must pass foreign-firmware rejection and
manifest verification before a guarded physical capture.

## Physical capability result

The [protected xHCI capture](../hardware/lab/observations/qotom-native-xhci-20260911/README.md)
returned status 0 and DWORDs `01000080,07000820,84000054,0200000a,200077c1,00003000,00002000`
in register order. In particular, HCSPARAMS3 and HCCPARAMS differ from defaults
used in synthetic fixtures; future binding must use the retained hardware values.
Both resource refreshes and protected replay passed, and FreeBSD recovered with
the request consumed. No xHCI writes or pointer-following occurred.

## Bounded extended-capability reader

`boot/qotom-xhci-legacy.h` refreshes all seven captured capability words and PCI
binding before following xECP. The [Linux xHCI extended-capability definitions](https://github.com/torvalds/linux/blob/master/drivers/usb/host/xhci-ext-caps.h)
confirm that xECP uses DWORD units from BAR, while each next field is a forward
DWORD displacement from the current header. The observed HCCPARAMS `0x200077c1`
therefore starts the walk at offset `0x8000`.

The closed reader accepts only aligned offsets `0x8000..0xfffc` inside the
captured 64-KiB resource and at most 48 headers. Nonzero next fields strictly
advance; bounds checks prevent wraparound or escape. IDs 0 and 255 reject.
Other IDs are retained without interpreting payloads. Duplicate legacy structures,
legacy control outside the resource, and a next header overlapping that control
reject. The reader samples legacy control/status at legacy offset+4 only after
the list terminates, then refreshes PCI and capability binding again.

At most 87 reads occur. All output, including staged headers, stays zero on
failure. Zero legacy offset means no legacy structure was found, not ownership.
The tests cover a 48-header list, all 87 read-failure positions, relative offsets,
resource boundaries, missing/duplicate/overlapping legacy structures, capability
drift and failed-publication rules. List and control samples remain sequential;
no ownership write or continuing firmware-exclusion claim is added. Native integration, capture decoding and physical list observation remain
outstanding.

## Extended-read mapping gate

`hardware/lab/qotom-xhci-ext-window.h` gives the bounded reader a separate
read-only aperture for aligned physical addresses `d0908000..d090fffc`. Each
transaction derives the physical page from the accepted address and maps it
supervisor-only, NX and UC. It restores the exact saved leaf and invalidates
before publishing the private sample. Mapping or control interference terminates
instead of returning a sample; a rejected address performs no mapping or load.
The existing seven-register capability window is unchanged.

The extended arming gate binds all seven retained physical capability DWORDs
and reuses the xHCI PCI identity, firmware, root and 64-KiB alias checks through
private staging. Failed rearm clears authority. Arming does not access hardware;
the collector still refreshes the resource before following links. Tests exercise
every byte offset through the resource boundary, every admitted DWORD read across
all eight pages, restoration and interference, every single-bit capability
mutation, and the existing resource/ECAM alias and failed-rearm cases. These
checks do not establish continuing firmware or AP exclusion.
