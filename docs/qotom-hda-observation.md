# Qotom HDA global observation

The native inventory identifies index 5, 00:1b.0, Intel `0f04:8086`, class/revision
`0403000e`, Command `0006`, and 64-bit BAR `d0910004:00000000`. FreeBSD identifies
the same controller with a 16 KiB aperture at `d0910000` and attached Realtek and
Intel codecs. Its bus mastering is a remaining part of issue #330.

## Register contract

[Intel 329670-002](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf),
sections 15.5.3, 15.5.13–14 and 15.6.1–6/12, supplies the identity, BAR and global
register contract. The observer samples GCTL (DWORD at 8), GCAP (word at 0),
VMIN/VMAJ (bytes at 2/3), INTCTL (DWORD at 20h), then GCTL again. GCTL.CRST must
report one before other registers are accessed and in the final GCTL sample.

The datasheet has conflicting stream-count descriptions: section 15.2 says
three input/output streams, section 15.6.1 gives default GCAP `4401` but describes
three, and table 123 lists four of each. The observer retains actual GCAP rather
than choosing stream-register addresses from these conflicting descriptions.

## Collector and validation

`boot/qotom-hda-observation.h` requires the exact captured identity, class,
header type, MSE and both BAR words. Six PCI reads before and after the six MMIO
reads check that binding, for exactly 18 reads on success. Unrelated Command
and PCI Status bits may vary. The MMIO callback receives the required width in
bytes and must return zero-extended values. The address selector admits only
five exact offset/width pairs; it does not grant mapping authority.

Statuses distinguish arguments, initial header rejection, failed configuration
reads, resource drift, failed MMIO reads, all-ones absence, nonzero bits above
the requested width, and CRST clear. Every failure publishes zero and stops at
the first rejected read. Successful GCTL samples may differ in other bits;
they are sequential observations, not an atomic snapshot or a halt certificate.
All raw capability, version and interrupt fields are retained without silently
interpreting unsupported values as an admitted platform.

Tests check exact order/widths, all 18 failure positions, every identity/resource
bit at entry and final revalidation, every payload bit, narrow-read bounds,
all-ones reads, initial/final reset, changed GCTL, invalid callbacks and all
16 KiB offsets with widths zero through eight. The collector has no write or
polling callback. Physical capture is retained below; stream/ring state, shutdown and BME policy
remain pending. This helper
alone does not establish transaction drain, firmware/AP exclusion or DMA
containment.

## Read window and arming

The read window maps only page `d0910000` using leaf `80000000d0910019`
(supervisor, read-only, NX, UC). Each read passes its exact width to the trusted
load primitive. It checks controls, saves the original aperture leaf, maps and
invalidates, samples privately, restores the exact leaf, invalidates again and
checks final controls. Mapping or control interference terminates after cleanup.
A failed load publishes no value. No page-table root switch is performed.

The arm gate binds copied firmware, the original roots, exact device/resource
and MSE, and excludes all 4096 low-memory mappings to every page in the 16 KiB
resource. Rejected rearms clear all authority. Arming performs no MMIO access
or page-table mutation. Tests cover exact widths, all four pages of aliases,
failed loads, missing callbacks, invalid apertures and mapping interference.

## Native capture

The opt-in `--hda-observation` build requires `--ahci-bme` and runs only after
the preceding SATA stage returns successfully. It arms the HDA reader for native
header index 5, serializes ECAM and MMIO reads through the restored aperture,
and disarms both contexts before emitting `HDA`. Local arm rejection is status
9. A noinline native primitive performs only the selected byte, word or DWORD
load. All nonzero outcomes terminate with `qotom-hda`.

The protected runner fingerprints the HDA decoder and retains `hda.json`. It
requires the successful prior SATA record, exact framing/order, bounded raw
values, CRST set on success, zero payload on failure, and the corresponding
terminal. Earlier-stage projections do not replace the actual HDA terminal.
Tests exercise valid samples, every reachable failure, contradictory payloads,
width bounds, missing/duplicate records, failed preceding SATA and changed
GCTL. They do not replay device operations.

## Physical capture

The retained [Win7 Legacy observation](../hardware/lab/observations/qotom-native-hda-20260911/README.md)
reports status 0, GCTL `1` before and after, GCAP `4401`, VMIN `0`, VMAJ `1`,
and INTCTL `0` (hexadecimal). GCAP advertises four input and four output streams,
zero bidirectional streams and 64-bit addressing. Both resource revalidations
passed. No stream/ring read or HDA write was performed.

FreeBSD recovered automatically after 34.300 seconds of serial quiet with a
changed boot time and consumed request. Independent SSH verified installed
hashes and request=none. The build passed 115 manifest hashes, the eight-site
MSR audit, load-width disassembly and QEMU foreign-firmware rejection; all 51
protected groups passed before building, and the retained physical replay
passed afterward. The terminal remains `qotom-platform-pending`.
