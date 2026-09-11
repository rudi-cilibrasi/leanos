# Native Qotom Advanced Features observation

The protected Win7 Legacy USB boot matched native BSP and PCI inventory,
collected all 47 capability headers, then refreshed identity and lists before
AF observation. EHCI index 10 (`00:1d.0`) returned status 0, AF offset 152,
raw control/status dword 0. Thus its pending bit was clear at this sampling
instant. The other 15 functions returned status 1 (no AF structure).
No controller reset or PCI configuration write was requested by the observer.
FINAL remained `qotom-platform-pending`.

FreeBSD recovered automatically after 34.31699377199402 seconds of serial
quiet; boot time changed from 1789146758 to 1789147616. The request was consumed.
Independent read-only SSH verified installed ELF and `request=none`.
Serial was FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`e369f33024ec667d125b9a92d9e5bedf7936b53f4f3e6018d3e3a733f13b10a2`.
Build provenance remains def5fd0 with dirty integration sources; runner was
7d6348d. Guarded installation checked USB serial 11758C40, staged and old
hashes, backed up boot files, and verified filesystem and installed hashes.

A momentarily clear pending bit does not prove stopped DMA or exclude a later
firmware/controller request. USB legacy ownership, stop/drain and reset recovery
contracts remain unresolved under issue #330. This observation establishes no
platform/CPL3 admission or operator-visible display result.
