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
how this BIOS switches port ownership. The observations below now include a cooperative ownership request and legacy
SMI disable. Controller stop and reset remain outstanding. Issue #330 remains open.

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
and exact write width/address/value. The native write aperture, checked timing backend and physical handoff evidence
are described below. Controller stop remains outstanding.

## Single-byte write aperture candidate

`hardware/lab/qotom-ehci-semaphore.h` supplies a separate transaction type for
one OS-semaphore request. It accepts only BDF `00:1d.0`, offset `0x6b`, value
`1`, and consumes its armed state before checking the request. It temporarily
maps ECAM page `0xe00e8000` supervisor-only, writable, NX and UC, then invokes
a trusted byte-store callback at aperture offset `0x6b`. Hardware Accessed and
Dirty changes are permitted. The original leaf is restored and invalidated
before post-checking controls and returning. Mapping or control interference
terminates after the restoration attempt. A failed store can still have affected
the device; neither rejection nor mapping restoration implies rollback.

`qotom-ehci-semaphore-arm.h` binds authorization to the exact captured identity,
BAR, three capability dwords and one-entry legacy list/control observation.
It checks the firmware fixture, root/ancestors, aperture ownership and absence
of ECAM/EHCI aliases. It performs no device access and clears old authority on
rejection. The handoff collector must refresh the hardware binding before using
this authorization; immutable views, serialized callbacks and firmware/AP
exclusion remain caller obligations.

Ordinary and sanitizer transaction tests check every byte value and selector,
a second request after consumption, failed stores, mapping restoration and
terminal interference. Arm tests reject all 4096 ECAM and EHCI alias slots and
mutations to the captured legacy/capability fields. Native store/timing wiring and the protected physical capture are described below.

## Checked ten-millisecond delay

`qotom-pm-delay.h` binds the pinned FADT's 24-bit timer at I/O port `0x408`
and its 32-bit access format, then rechecks LPC identity, Command `0x0007`
and ACPI-base decode `0x403`. It performs no timer read while arming and
revokes prior authority if the binding fails. Native resource stability and
firmware exclusion remain assumptions.

The [ACPI timer specification](https://uefi.org/specs/ACPI/6.5/04_ACPI_Hardware_Specification.html)
defines a 3,579,545-Hz free-running counter. The helper accepts only the
handoff's ten-millisecond delay. It requires 35,797 elapsed ticks: the rounded-up
interval plus one tick to cover unknown phase at the initial sample. It allows
24-bit wraparound, rejects upper bits, backward elapsed samples and differences
of half a cycle or more, and caps each delay at one million reads including
the initial sample. A read failure or exhausted bound revokes the context.

The arithmetic assumes a continuous standards-compliant clock and bounded
callbacks. It cannot detect whole counter cycles hidden between samples or
prove a wall-time upper bound against arbitrary firmware pauses. No timer or
event register is written. Tests cover the tick threshold, wraparound, stopped
and backward clocks, read failures and failed LPC binding. Native I/O wiring and the protected handoff result are described below.

## Opt-in native handoff experiment

The builder's `--ehci-handoff` requires `--ehci-legacy` and creates the separate
`build/qotom-handoff-lab` image. After retaining the complete initial legacy
observation, the native helper arms the reader, firmware-bound PM delay and
single-byte writer. It invokes the bounded request and revokes all four
contexts before emitting `EHCI-HANDOFF`. Failed local arming has distinct
statuses 11–13; request failures retain their diagnostic fields and stop at
`qotom-ehci-handoff`. A successful observation still reaches
`qotom-platform-pending`. No SMI change or controller stop is added.

The runner's matching option fingerprints the handoff decoder before arming
and checks it again afterward. The decoder requires the preceding complete
legacy/capability observations, exact writer binding where the request was
reached, bounded poll counts and consistent diagnostic fields/terminal. It
retains `ehci-handoff.json`. Hardware operations are not independently replayed;
the preceding inventory remains subject to generated replay. Synthetic protected
capture tests exercise success, failures, malformed framing and contradictory
attempt/poll/semaphore fields. The [physical handoff capture](../hardware/lab/observations/qotom-native-ehci-handoff-20260911/README.md)
reported release at the first poll and passed final refresh: support `0x01000001`,
control/status `0x2000`. The full protected replay agrees, and FreeBSD recovered
automatically with the one-shot request consumed. This is a semaphore observation;
the subsequent SMI step is described below. Controller shutdown, outstanding
transactions and DMA containment remain unresolved.

## Bounded legacy SMI disable candidate

`boot/qotom-ehci-smi.h` follows a successful handoff with another complete
capability/list refresh. It requires the captured single legacy structure with
OS ownership set and BIOS ownership clear. Enable bits must agree with the
handoff result; status bits may change asynchronously. Reserved bits reject.

[EHCI 1.0 section 2.1.8](https://www.intel.com/content/dam/www/public/us/en/documents/technical-specifications/ehci-specification-for-usb.pdf)
defines enable mask `0x0000e03f`, read-only status mask `0x003f0000` and
write-one-to-clear status mask `0xe0000000`. The candidate writes one zero dword
to `00:1d.0` offset `0x6c`. This disables enables without acknowledging status.
A final complete refresh must retain the ownership/list binding and read all
enables clear; status bits can remain set. The result preserves both control
samples and whether a write was attempted, including ambiguous write failure.

The callback sequence allows at most 114 reads and one write. It performs no
rollback, controller stop or reset, and does not establish firmware exclusion
or DMA containment. Tests cover all 512 enable combinations, asynchronous
status changes, every refresh read failure, ownership reassertion, reserved
bits, ignored writes and failed writes that nevertheless take effect. Native
write-aperture integration and physical SMI-disable evidence are described below.

## Native SMI-disable experiment

`qotom-ehci-smi-window.h` grants a separate consumed transaction for one zero
DWORD at `00:1d.0` offset `0x6c`. The temporary UC, writable, supervisor/NX
mapping is restored and invalidated before returning. Arming binds the exact
controller/capabilities, successful handoff result, firmware and root/alias
checks. The bounded collector refreshes the hardware again before writing.
Tests reject other selectors, every nonzero value bit, reuse, failed rearming
and mapping/control interference, including all ECAM/EHCI alias slots.

The builder's `--ehci-smi` requires `--ehci-handoff` and creates
`build/qotom-smi-lab`. Native code invokes the SMI helper after retaining the
successful handoff record, revokes the contexts, and emits `EHCI-SMI` with
status, attempt and both control samples. Local arm failures use statuses 8–9.
The runner fingerprints its matching decoder and retains `ehci-smi.json`.
Validation distinguishes disabled enable bits from retained status bits and
preserves a failed SMI terminal alongside the earlier inventory replay.
The compiled native primitive is one DWORD store. The [physical SMI capture](../hardware/lab/observations/qotom-native-ehci-smi-20260911/README.md)
read back control/status changing from `0x2000` to `0`, with final ownership
refresh accepted. Protected replay agrees, and FreeBSD recovered automatically.
This does not establish controller halt or DMA containment.

## Operational-state collector before shutdown

`boot/qotom-ehci-operational.h` requires the successful SMI-disable result and
exact captured capabilities. It refreshes the full PCI/capability/legacy binding,
requires OS ownership with BIOS ownership clear and all legacy SMI enables clear,
then samples USBCMD, USBSTS, USBINTR and CONFIGFLAG. Another complete refresh
must accept the ownership and disabled enables before any result is published.
Asynchronous legacy status changes are allowed. Any failure publishes zero fields.

[EHCI 1.0 table 2-8](https://www.intel.com/content/dam/www/public/us/en/documents/technical-specifications/ehci-specification-for-usb.pdf)
defines DWORD operational accesses relative to CAPLENGTH. The checked captured
CAPLENGTH `0x20` produces addresses `0xd0915020`, `0xd0915024`, `0xd0915028`
and `0xd0915060`. The helper allows at most 118 reads, with separate callbacks
for capabilities and operational samples. It grants no mapping or write authority.
The restricted mapping, native wiring and protected physical result are described below.

The four values are sequential raw observations, not an atomic snapshot. Reserved
bits are retained for review, while all-ones reads reject. No operational write,
controller halt, reset or DMA admission is added. Tests cover every read-failure
position in the pinned one-entry list, ownership/SMI/BAR/capability drift, all
CAPLENGTH bytes and in-page offsets, raw sample bits and failed-publication rules.

## Restricted operational read mapping

`hardware/lab/qotom-ehci-operational-window.h` supplies a distinct read-window
transaction admitting only the four selected DWORD addresses. It maps the EHCI
page read-only, supervisor-only, NX and UC, performs one trusted load, and restores
and invalidates the saved leaf before publishing the value. It permits hardware
Accessed updates; permission, root or restoration interference terminates after
the restoration attempt. A failed load returns no value.

`qotom-ehci-operational-arm.h` requires the exact captured capabilities and a
successful SMI-disable result. It reuses the capability reader's firmware, root
and alias validation through private staging, then populates the distinct window.
No mapping or device access occurs while arming. Failed rearming clears all
previous authority. The collector still refreshes device binding and ownership
before its operational samples; immutable views and serialized trusted callbacks
remain caller obligations. Tests cover all in-page address offsets, ECAM/EHCI
alias slots, capability and SMI-result mutations, load failures, restoration and
terminal interference.

## Native operational observation

The builder's `--ehci-operational` requires `--ehci-smi` and creates a separate
`build/qotom-operational-lab` image with all four new source files in its manifest.
After the successful SMI record, native code rearms the capability and operational
readers, invokes the bounded collector, and revokes all read contexts before
emitting `EHCI-OPERATIONAL`. Local arming failures use statuses 8 and 9. Successful
sampling still terminates at `qotom-platform-pending`; failed sampling terminates
at `qotom-ehci-operational`. No controller stop or reset is requested.

The protected runner fingerprints the matching decoder before arming, rechecks
it after recovery, and retains `ehci-operational.json`. The decoder requires the
complete successful SMI prefix, canonical scalar fields, exact record order and
consistent failure publication. Earlier generated inventory replay is retained,
and the actual operational terminal is restored after prefix projections. Raw
observations are not claimed to be independent hardware replay or atomic samples.

The [physical operational capture](../hardware/lab/observations/qotom-native-ehci-operational-20260911/README.md)
retained command `0x80000`, status `0x1000`, interrupt enable `0` and configuration
flag `0`. Run/Stop was clear and HCHalted set when sampled, without an operational
write. Final ownership/SMI refresh and protected replay passed, and FreeBSD
recovered automatically. This changes the next shutdown review: the observed
controller was already halted. Continuing exclusion and system-wide DMA
containment still require separate evidence.

## Bus-master disable candidate after a stopped sample

The physical sample justifies examining a BME-only transition without a redundant
operational stop. EHCI 1.0 section 2.3.1 ties HCHalted to completion of current and
pipelined USB transactions. This is controller state, not independent evidence
of all fabric posted writes completing or continuing firmware exclusion.

`boot/qotom-ehci-bme.h` requires the exact captured stopped operational result
and PCI Command `0x0406`, then refreshes ownership, disabled SMIs and the operational
sample. A separate fresh Command read must still be `0x0406`. It requests one
16-bit write of `0x0402` at `00:1d.0` offset 4, verifies readback, repeats the
complete operational collector, and checks Command again. This clears only BME,
retains MMIO decoding and INTx disable, and avoids writing adjacent PCI Status.
Linux's [PCI bus-master helper](https://github.com/torvalds/linux/blob/master/drivers/pci/pci.c)
also uses a word-sized Command update to clear the master bit.

The operation allows at most 239 reads and one write. It records attempted
writes and command observations, including ambiguous failure; it never restores
BME as rollback. Unexpected state rejects. Tests cover all 51 read positions in
the captured one-entry list, every prior operational bit mutation, command and
status-halfword preservation, ignored writes, failed writes with effects, and
post-write restart or BME reassertion. Native word-store authority and physical
execution are described below. Continuing device/firmware assumptions remain
outstanding; no system-wide DMA containment or platform admission follows.

## Consumed word-store mapping

`hardware/lab/qotom-ehci-bme-window.h` permits only the BME-clear request at
`00:1d.0` offset 4, value `0x0402`, through a trusted 16-bit store callback.
It consumes its armed flag before validation, temporarily maps the ECAM page
UC, writable, supervisor-only and NX, then restores and invalidates the original
leaf before reporting the store result. Hardware Accessed/Dirty updates are
allowed; other mapping or control interference terminates after restoration.
Failed stores can have taken effect and do not authorize retry or rollback.

`qotom-ehci-bme-arm.h` binds the exact controller, capabilities, PCI Command,
successful SMI disable and captured stopped-state sample to the firmware and
root/alias checks. Rejection clears old authority. Arming performs no hardware
access; the helper still refreshes all device state before its write. Tests
reject all other 16-bit values, BDF/offset changes, reuse, failed stores, stale
samples, ECAM/EHCI aliases and root/leaf interference. Native store wiring and
protected physical validation are described below.

## Native BME-clear experiment

The builder's `--ehci-bme` requires `--ehci-operational` and produces a separate
`build/qotom-bme-lab` image. Native code rearms the capability and operational
readers plus the consumed word writer, invokes the bounded helper, and revokes
all contexts before `EHCI-BME`. Local arming failures use statuses 9–11.
The compiled primitive uses one `mov WORD PTR [rsi],dx`; it does not store the
adjacent PCI Status halfword. Success still terminates at qotom-platform-pending.

The protected runner fingerprints the decoder and retains `ehci-bme.json`.
Validation requires the complete operational prefix, exact stopped sample and
captured Command before a helper outcome, consistent attempted/before/after
fields, and the matching terminal. Failed writes and readback remain diagnostic
observations, including a write that took effect despite reported failure.
The actual BME terminal replaces the preceding replay projection's terminal.
Synthetic protected tests cover those outcomes and reject missing, duplicate,
malformed, out-of-range and contradictory records. The physical result is retained below.

The [physical BME capture](../hardware/lab/observations/qotom-native-ehci-bme-20260911/README.md)
reported Command `0x0406` to `0x0402` with status 0. Final ownership, disabled
SMIs, stopped-state refresh and Command readback passed. The full protected
replay agrees, and FreeBSD recovered automatically with the request consumed.
This verifies the bounded transition on EHCI; other devices and continuing
firmware/AP exclusion remain outside this observation.
