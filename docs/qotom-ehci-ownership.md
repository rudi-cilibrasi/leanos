# Qotom EHCI ownership before shutdown

The native AF capture identifies EHCI `00:1d.0`, `8086:0f34`, BAR0
`0xd0915000`, Command `0x0406`. Memory decoding and bus mastering are enabled.
Its AF pending bit was clear at one instant. That does not establish firmware
ownership exclusion or a stopped controller.

The [recovered FreeBSD topology](../hardware/lab/observations/qotom-freebsd-usb-topology-20260911/manifest.json)
places USB stick serial `11758C40`, the mouse, hub and keyboard under xHCI
`00:14.0`. FreeBSD does not enumerate EHCI. These are post-recovery OS
observations; they must not replace the native sixteen-function inventory or
justify skipping EHCI during firmware-time quarantine.

## Required read path

EHCI's HCCPARAMS at BAR0+8 contains the extended capability pointer in bits
15:8. This points into PCI configuration space. The legacy support capability
contains ownership semaphores; its control/status dword follows at offset+4.
See the primary Linux [register definitions](https://github.com/torvalds/linux/blob/master/include/linux/usb/ehci_def.h)
and [handoff implementation](https://github.com/torvalds/linux/blob/master/drivers/usb/host/pci-quirks.c).
The conventional PCI list collected earlier is a different list and cannot
supply this pointer. Guessing a familiar legacy offset is insufficient.

The current lab window admits only ECAM addresses `0xe0000000..0xefffffff`.
It correctly rejects BAR0+8. A new read path must bind the fresh EHCI identity,
header layout, enabled memory decode and BAR0 to the native inventory, then
validate effective UC mapping, alias exclusion and the existing root/leaf
restoration contract for the separate MMIO page. Do not widen the ECAM
address gate globally. The initial bounded MMIO observation should retain the
capability base, HCSPARAMS and HCCPARAMS before following a checked configuration
pointer. Operational register offsets must derive from the observed CAPLENGTH.

## Ownership is separate from an idle sample

Linux requests ownership through the OS semaphore, waits for BIOS ownership to
clear, disables legacy SMIs, and stops the controller. Its fallback can forcibly
clear BIOS ownership after a timeout. Such a fallback cannot prove firmware
cooperation for LeanOS. A bounded handoff timeout must leave admission closed.
A later stop must verify the controller's halt state, account for outstanding
transactions and firmware/AP access, and preserve the protected recovery path.

Intel's [329670-002 datasheet](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf),
section 14.3, printed page 340, describes EHCI as a legacy alternative to xHCI.
That is consistent with the differing observations, but does not prove when or
how this BIOS switches port ownership. No new MMIO read, ownership write,
controller stop or reset was performed for this audit. Issue #330 remains open.

## Capability collector

`boot/qotom-ehci-capabilities.h` binds its candidate to the captured EHCI BDF,
identity, class/revision, endpoint layout, memory-decode bit and exact BAR0.
It rechecks those five configuration dwords before reading BAR0 offsets 0, 4
and 8. Success retains all three raw capability dwords. Any failed read or
validation publishes zero fields. The format check requires EHCI 1.0, a
non-overlapping aligned CAPLENGTH, and a nonzero port count. These are candidate
checks, not general EHCI compatibility claims.

The collector delegates MMIO access to a caller-supplied callback. The callback
must separately establish the UC mapping, alias exclusion and restoration
contract described above; this component does not authorize arbitrary MMIO.
No native adapter or hardware capability-register capture exists yet. Tests
exercise read failures at every position, identity/BAR drift, all CAPLENGTH
bytes, and rejection of addresses outside the three selected offsets in both
ordinary and sanitizer builds.

## Separate mapping candidate

`hardware/lab/qotom-ehci-arm.h` binds the immutable native EHCI header and the
exact firmware fixture to the existing root/ancestor checks. It additionally
rejects every present leaf mapping the EHCI page, regardless of permissions.
Failed rearming clears window authority. Arming performs no device access.
The caller must keep the header, firmware and page-table views stable and
provide fresh resource checks through the collector before device reads.

`qotom-ehci-window.h` uses a separate window type and admits only physical
addresses `0xd0915000`, `0xd0915004` and `0xd0915008`. Its temporary leaf is
supervisor-only, read-only, NX and UC under the checked PAT layout. The
transaction restores the saved leaf and invalidates before publishing a read;
root or leaf interference follows the terminal fault policy. Existing ECAM
address checks are unchanged. Trusted native callbacks and firmware/AP
exclusion remain explicit assumptions.

Ordinary and sanitizer tests check every leaf slot for aliases, every offset
within the page against the three-address limit, failed loads, control drift,
leaf interference and restoration failure. Native image wiring and a physical
EHCI capability capture are still required before using this candidate.
