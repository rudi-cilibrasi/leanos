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

The original configuration-space lab window admits only ECAM addresses `0xe0000000..0xefffffff`.
It correctly rejects BAR0+8. The separate read path described below must bind the fresh EHCI identity,
header layout, enabled memory decode and BAR0 to the native inventory, then
validate effective UC mapping, alias exclusion and the existing root/leaf
restoration contract for the separate MMIO page. Do not widen the ECAM
address gate globally. The initial bounded MMIO observation retains the
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
how this BIOS switches port ownership. The observations below add bounded reads; no ownership write, controller stop
or reset has been performed. Issue #330 remains open.

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
The native adapter is described below; the physical result is linked below. Tests
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
leaf interference and restoration failure. The builder's `--ehci-capabilities` option requires `--af-observation` and
uses the separate `build/qotom-ehci-lab` directory. Native image wiring calls
the collector after the accepted complete inventory and AF capture. The ECAM
and EHCI readers serialize their temporary mappings through the same aperture,
restoring it between operations. Both windows are disarmed before emitting
`EHCI-CAPS`; failure stops at `qotom-ehci-capabilities`.

The runner's matching flag fingerprints its decoder and retains
`ehci-capabilities.json`. Decoding requires the preceding complete AF sequence,
checks field bounds/format and failure publication, and preserves the actual
terminal alongside the inventory replay projection. Failed hardware reads
remain observations, not independently replayed results. A native fault without
a complete record fails capture validation. Synthetic protected-capture tests
cover success, malformed records, and every publishable failure status.
The [physical capture](../hardware/lab/observations/qotom-native-ehci-20260911/README.md)
returned capability base `0x01000020`, HCSPARAMS `0x00200008` and HCCPARAMS
`0x00036881`. Thus the observed extended-list pointer is `0x68`; the subsequent
legacy capture below follows that pointer. FreeBSD recovered automatically.

## Bounded extended-list reader

`boot/qotom-ehci-legacy.h` refreshes the same PCI binding and three MMIO
capability values before following the observed HCCPARAMS pointer. It compares
those values to the preceding capability sample, then reads at most 48 aligned
configuration headers in `0x40..0xfc`. A visited-slot set rejects cycles;
zero or all-ones IDs, invalid pointers and duplicate legacy structures fail.
Unknown nonzero IDs are retained as headers without interpreting their payloads.
A legacy structure must fit its control/status dword inside configuration space
and must not overlap another list header. Only after the entire list terminates
does the reader sample that control/status dword.

The read-only operation uses at most 57 reads including refresh. Rejections
publish zero count, legacy offset and control/status; partially staged array
bytes are not authoritative. Success with legacy offset zero means no legacy
structure was found in the observed list. It does not establish ownership.
The support and control/status fields are sequential observations and may
change asynchronously. No semaphore write, SMI change or reset is performed.
The builder's `--ehci-legacy` option requires `--ehci-capabilities` and uses
`build/qotom-legacy-lab`. It rearms the checked window, refreshes the same
capability sample, and emits `EHCI-LEGACY` plus ordered `EHCI-EXT` records with
both windows disabled. Failure publishes no list and stops at
`qotom-ehci-legacy`.

The runner's matching option fingerprints the legacy decoder and retains
`ehci-legacy.json`. Validation follows the preceding HCCPARAMS pointer, checks
all links, duplicate legacy structures, overlap, selected offset and terminal
framing. The remaining prefix still passes the preceding capture decoders and
generated inventory replay. Failed reads remain observations rather than
independently replayed hardware events. Synthetic full protected tests cover
success, corrupt records and all publishable failure statuses. The [physical legacy capture](../hardware/lab/observations/qotom-native-legacy-20260911/README.md)
retained one header at `0x68`, raw `0x00010001`, and control/status
`0x00082005`. Its complete protected replay matches the native inventory and
legacy metadata. FreeBSD recovered automatically; ownership remains unresolved.

## Bounded semaphore request candidate

`boot/qotom-ehci-handoff.h` adds a callback-based request sequence, without
native hardware wiring. It refreshes the capability registers and complete
extended list and requires exact agreement with the preceding observation,
including control/status. It accepts only BIOS-owned, OS-clear legacy support
with zero reserved semaphore bits. The captured `0x00010001` satisfies that
initial semaphore shape; it does not establish firmware cooperation.

The only write callback receives one byte, value `1`, at the validated legacy
offset plus three, on `00:1d.0`. It requests OS ownership without writing the
BIOS byte or the control/status dword. This follows the request mechanism in
the linked Linux implementation. Unlike its timeout fallback, this candidate
never forcibly clears the BIOS semaphore. A failed callback may have changed
hardware; the diagnostic result records that a write was attempted.

After each requested ten-millisecond delay, it reads legacy support, requiring
the OS bit to remain set and all non-semaphore bits to remain unchanged.
It permits at most 100 polls. BIOS release triggers another full capability
and extended-list refresh; the final support must still show OS ownership and
BIOS release. Final control/status is retained without requiring equality with
its pre-request value, since firmware may change it during handoff. Timeout,
read/delay failure, lost OS request, changed structure or failed final refresh
rejects the sequence. No rollback or further write follows rejection.

The bound is 214 reads, one byte write and 100 delay calls requesting 1000 ms
in total. Actual elapsed-time bounds depend on bounded callbacks and firmware
execution. The caller must supply real delays, stable PCI resources, serialized
mapping transactions and immutable nonaliasing inputs. An observed semaphore
release does not itself prove firmware exclusion, controller halt, outstanding
transaction drain or DMA containment.

Synthetic tests cover release at every poll, timeout, every poll read/delay
failure, every refresh read failure, changed support bits, BIOS reassertion
and exact write width/address/value. Native write-aperture authority, a checked
timing backend, protected hardware execution, SMI policy and controller stop
remain to be integrated. No physical handoff was attempted by this candidate.
