# Native Qotom graphics-ring state capture — 2026-09-12

A protected Win7 Legacy boot completed the bounded, read-only Valleyview
graphics observation at PCI `00:02.0` (inventory index 1). LeanOS sampled five
32-bit registers for each render, video and blitter ring twice. Both samples
reported tail, head, start and control as zero and mode as `0x200`. The decoder
therefore classified all three rings as stable, invalid/idle and empty.

The observer mapped only the exact graphics BAR0 aperture through a temporary
supervisor, read-only, NX, uncacheable window. It performed 16 PCI-header reads,
30 MMIO reads and 16 final PCI-header reads. Display memory and I/O decoding
remained enabled and graphics bus mastering remained enabled. This capture is
read-only state evidence; it does not establish graphics ownership, firmware or
AP exclusion, posted-write drain, DMA quarantine, or platform/CPL3 admission.
The terminal remains `qotom-platform-pending`.

The retained `header-rejection` attempt records an initial status-7 rejection.
That attempt expected the recovered FreeBSD PCI Command value `0x0407`, but the
boot-time PCI header captured Command `0x0007`; FreeBSD adds Interrupt Disable
later. Binding the arm gate to the captured boot state fixed the mismatch while
retaining the exact device, BAR and command checks. The successful observation
then returned status 0. The rejected record's zero-filled payload is a failure
sentinel, so its derived stability, ring-state, decode-preservation and
BME-preservation claims are all false.

FreeBSD recovered automatically after 34.324949994974304 seconds of serial
quiet, boot time 1789239099 to 1789240257, with the one-shot request consumed.
Independent SSH verified USB serial 11758C40, the installed hashes, backup,
`request=none`, no remaining USB mount, and the recovered Intel graphics device
with memory and I/O BARs enabled in D0. Serial was FTDI/null modem COM1 at 38400
baud, 8N1, no flow control.

ELF SHA256:
`50826885480d163d5eadb7f9614d95fe969859fb5e848c22659de4cbb7845827`.
Successful raw capture SHA256:
`b6ecdf910d348985d47d0ef84745f52d3d6828c3bfdaed426b623837856ef813`.
Rejected raw capture SHA256:
`6a31fa01a7aa319acd7b531afa13be612f67404bb844164b201d986bf3d1fe2c`.
Build and runner revision: `3164a66bb3670a14446a8640eb9bed7266f3c85f`.
The clean build manifest contains the dependency-chain hashes. The ordinary and
pinned sanitizer capability tests, protected projection, canonical image build,
guarded USB install, FAT check, physical runner and recovery inspection passed.
