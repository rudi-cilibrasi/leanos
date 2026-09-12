# Native Qotom xHCI final-comparison diagnosis

The v2 protected Win7 Legacy boot observed BIOS-clear/OS-owned support
`0x01000801` at poll one, then rejected the final list comparison. The added
verification fields identify header index 2 at offset `0x8040`: expected
`0x00010cc1`, observed `0x00000cc1`. Both complete collectors succeeded; the
capability ID and relative next pointer remained unchanged.

The differing bit is CMD_RING_RUNNING (bit 16) in XECP_CMDM_STS0. Intel
329670-002 section 14.7.138, pages 473–474, defines it as read-only live status.
The old comparison incorrectly treated that status as invariant. This capture
motivates comparing the documented list fields separately from live status.
The terminal remains `qotom-xhci-handoff`, status 10; zero final control means
unpublished data, not a hardware control sample. No completed handoff or DMA
quarantine is claimed from this rejected experiment.

Protected replay accepted the rejection and FreeBSD recovered after
34.30960111800232 seconds of serial quiet. Boot time changed from 1789160798 to
1789161776; the request was consumed. Independent read-only SSH verified hashes
and request=none, then unmounted. Serial was FTDI/null modem COM1 at 38400 8N1.

ELF SHA256:
`b5f4f7be7726a3ed92656cde891c537786fa758f71436c62c8f1a910e16803aa`.
Build provenance is 328a3e8 with dirty integration sources; runner was 9add482.
USB serial 11758C40, old/new hashes, backup and filesystem checks passed.
The only xHCI write was the ownership request; no legacy control/status or
operational write followed the rejected final check.
