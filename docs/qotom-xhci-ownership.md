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
no ownership write or continuing firmware-exclusion claim is added. The retained physical list observation below exercises the complete path.

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

## Native extended-list capture

`--xhci-legacy` requires `--xhci-capabilities` in both builder and protected
runner. The native stage arms the capability and extended readers separately,
refreshes binding, collects the bounded list, and disarms all contexts before
emitting `XHCI-LEGACY` and ordered `XHCI-EXT` records. Local statuses 11 and 12
identify capability-arm and extended-arm rejection. Collector status 1 is
unreachable from the native call site; every reported rejection has zero data.

The decoder validates relative DWORD links, exact captured capability binding
for collector results, structure selection, bounds, termination and the final
reason against the preceding complete capability observation. The protected
runner fingerprints the decoder and retains `xhci-legacy.json`. Synthetic
records exercise the 48-header limit, failed results, malformed links, duplicate
and overlapping structures, framing, terminal contradictions and changed prior
capabilities. These are protocol checks, not replay of hardware operations.
The experiment does not write xHCI registers or claim ownership or DMA isolation.

The native list stage is kept out of line. In the initially inlined image, an
address displacement in the enlarged capture path contained an additional raw
`0f 30` pair. The unchanged MSR-site audit rejected that image, including the
possible unaligned WRMSR entry. Separating the stage keeps its implementation
reviewable; the resulting linked image must still pass that exact byte audit.

## Physical extended-list result

The [protected extended-list capture](../hardware/lab/observations/qotom-native-xhci-legacy-20260911/README.md)
returned six headers and selected the legacy structure at `0x8460`. Its support
header is `0x00010801` (BIOS-owned set, OS-owned clear); control/status is
`0x00002001`. Both resource refreshes passed and FreeBSD recovered with the
request consumed. The retained-capture test revalidates all six relative links
and the selected control sample through the protected decoder. Cooperative
ownership handoff and subsequent xHCI shutdown remain outstanding.

## Bounded cooperative handoff helper

`boot/qotom-xhci-handoff.h` refreshes the complete capability/list observation
and requires exact agreement with the prior list and control sample. It accepts
an initial legacy support word only with BIOS-owned set, OS-owned clear and
reserved semaphore bits zero. One aligned DWORD MMIO request writes the sampled
support word with OS-owned set. This is the access width used by the
[Linux xHCI handoff implementation](https://github.com/torvalds/linux/blob/master/drivers/usb/host/pci-quirks.c)
when requesting ownership; Linux also gives BIOS one second to release it.

The helper waits at most 100 times for 10 ms and samples support after each
successful delay. Every sample must retain OS-owned and the original nonsemaphore
bits. Once BIOS-owned clears, a complete final list and PCI/capability refresh
must agree except for the two semaphore bits, and the final support sample must
still show BIOS-clear/OS-owned. The final control sample is retained separately;
it may change while firmware processes the request. No SMI-disable or continuing
firmware-exclusion claim follows from this helper.

The bound is 274 reads, one DWORD write and 100 delay callbacks. Timeout, drift,
read failure, delay failure and write failure reject. The helper never clears
BIOS-owned itself, writes control/status, resets a controller or rolls back.
A failed write may have taken effect, so output reports the attempted write
and last sample on failure. These fields are diagnostics, not authority.
Physical handoff validation remains outstanding.

Tests use the retained six-header list and a maximum 48-header list. They cover
every successful release delay, all 274 read-failure positions, every delay
failure, a timeout, an ignored write, write failure with a hardware side effect,
all non-BIOS support-bit changes, all prior header-bit mutations, final support
and list drift, absent legacy support, and malformed initial semaphore state.

## Ownership-request mapping gate

`hardware/lab/qotom-xhci-semaphore-window.h` admits one DWORD MMIO request:
address `0xd0908460`, value `0x01010801`. This sets OS-owned while retaining the
captured BIOS-owned bit and the other support fields. Every request consumes
its authority, including a rejected address or value. It maps physical page
`0xd0908000` supervisor-only, RW, NX and UC, performs one store, restores the
exact saved leaf, invalidates and checks controls before returning. Only hardware
Accessed/Dirty changes are allowed during the store. Interference is terminal;
a store failure can still have affected the device and does not trigger rollback.

Arming requires the successful captured six-header list, legacy offset `0x8460`,
control `0x2001`, all seven physical capability DWORDs, the xHCI PCI identity and
BAR pair, exact firmware tables, the validated active root, and exclusion of all
present aliases into the 64-KiB resource. Failed rearm clears all authority and
arming performs no device access. The handoff helper must refresh the complete
observation before invoking this window. Firmware/AP exclusion is still an
external assumption; the mapping checks do not establish it.

Tests exercise all byte offsets through the resource boundary, every address
and value bit mutation, all other low-word values, missing callbacks, repeated
requests, failed stores, restoration and terminal interference. Arming tests
cover every captured capability/header/offset/control bit, invalid list counts
and prior statuses, BAR drift, all 4096 leaf slots and all resource pages for
aliases, and failed rearm. Physical handoff remains outstanding.

## Native handoff integration

The builder and protected runner accept `--xhci-handoff` only with the complete
`--xhci-legacy` path. The native stage separately arms capability reads, extended
reads, the bounded ACPI PM timer and the consumed DWORD writer. Local statuses
11 through 14 identify those respective arm failures. It uses the existing
volatile 32-bit store primitive through the restricted MMIO window and disarms
all contexts before emitting `XHCI-HANDOFF`. Timeout or any rejected observation
terminates with `qotom-xhci-handoff`; success still ends at platform-pending.

The decoder requires the exact writer binding for helper results, validates
attempt/poll/support/control combinations for every reachable status, rejects
impossible native statuses, and preserves the actual final reason after prefix
replay. The runner fingerprints the decoder and retains `xhci-handoff.json`.
Protected mutations cover valid failure outcomes, contradictory success and
failure terminals, altered prior control, impossible poll counts and stale
support values. No physical handoff outcome is established by those synthetic
records; a protected boot is required after build verification.
