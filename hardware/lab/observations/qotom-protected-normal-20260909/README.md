# Three consecutive protected Qotom captures

Source revision f539506. The default runner selected dated, digest-bound
watchdog-leanos requests, consumed each request, armed 120 ticks, and loaded the
same lab ELF used by the earlier completed-run experiment. Every cycle emitted
exactly the expected BOOT and dma-identity FINAL rejection, stayed quiet for
about 34.3 seconds, reset, and returned through the consumed-request default to
authenticated FreeBSD SSH. Each boot epoch changed, and each USB environment
was verified consumed after recovery. No BIOS changes or operator resets occurred.

All three cycles passed the protected classifier directly, without a parser
correction or repeated hardware run. Raw bytes and timestamped events are
retained unchanged. The separate recovery.json files record OS/request facts
before classification; result.json adds the validated scenario and protection
result. The exact installed GRUB files are retained and were compared byte for
byte after sync, unmount, and read-only remount before this series.

COM1 settings: 38400 baud, 8N1, no flow control, FTDI/null-modem cable. Final
FreeBSD boot epoch: 1788989468. The USB was left unmounted with request=none.
The normal lab ELF SHA-256 is recorded in every result and load marker.

The independent loader and early-kernel stall trials in neighboring observation
directories establish the watchdog failure paths. These normal captures preserve
the rejection scenario and completed-run observation interval; recovery does not
turn that rejection into a CPL3 success or a canonical absorbing-halt capture.
