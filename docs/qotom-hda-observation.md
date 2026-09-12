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
polling callback. Native mapping/arm integration and physical capture remain
pending, followed by stream/ring state, shutdown and BME policy. This helper
alone does not establish transaction drain, firmware/AP exclusion or DMA
containment.
