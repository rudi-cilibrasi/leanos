# Native Qotom TXE host-visible BME capture — 2026-09-12

A protected Win7 Legacy boot completed the bounded host-visible Bus Master
Enable transition for the Intel Trusted Execution Engine at PCI `00:1a.0`
(inventory index 4). LeanOS refreshed the exact TXE identity, PCI Command and
two retained firmware-status words, performed one 16-bit Command write from
`0x0106` to `0x0102`, then repeated every read and observed the exact result.
Memory-space decoding and SERR# Enable remained set while host-visible
Bus Master Enable was clear.

The public Valleyview/Bay Trail datasheet describes TXE multi-context DMA that
is programmed by the private TXE processor, but it does not provide a
host-visible shutdown or drain protocol for that engine. Accordingly this
capture establishes only the PCI Command transition. It does not claim that
TXE private DMA stopped, that posted writes drained, that firmware was
excluded, or that DMA quarantine or platform admission was established. The
terminal remains `qotom-platform-pending`.

The first armed cycle was safely rejected by GRUB before LeanOS ran because the
installed request-prefix binding still named the preceding graphics image
digest. It consumed the one-shot request and chained to FreeBSD. The guarded
installer then changed all three embedded digest bindings to the TXE image,
verified the image, checksum, GRUB configuration and disarmed environment, and
the second cycle passed. The rejected raw trace is retained under
`stale-grub-rejection`.

FreeBSD recovered automatically after 34.314373954955954 seconds of serial
quiet, boot time 1789249245 to 1789249481, with the one-shot request consumed.
Independent SSH verified USB serial 11758C40, installed hashes, rollback
archive, `request=none`, no remaining USB mount, and the recovered Intel TXE
function. Serial was FTDI/null-modem COM1 at 38400 baud, 8N1, with no flow
control.

ELF SHA256:
`c2cbec01015efb0057c2c844e354e5ba40531c0642bdbe09ffe5b15a0b6f7931`.
Successful raw capture SHA256:
`92be7c5330bc9b9285e4be55131f2c97f70d24dc8b62f1330fe5f31e8283e13a`.
Rejected raw capture SHA256:
`2aec611884e7dd5676744c292eec80e583b9c195f1c88a0a8e89762b082760a6`.

A later reset retry also completed the full sequence and recovered FreeBSD.
Its root-port Device Status values were `16,16,16,16`, while the first capture
had `17,17,17,16`; the varying bit is the correctable-error-detected status
bit. The image correctly bound each pending check to its earlier observation
from the same boot, but the original host decoder assumed the first capture's
values. The corrected decoder now makes the same per-boot binding. The retry is
retained under `reset-retry`; its raw SHA256 is
`cab1e2aa83566041607903424366e19c074b5e11cb6b605441143297e08f0bbb`,
with 34.30736370803788 seconds of serial quiet and FreeBSD boot time
1789249481 to 1789250621.

Build and runner revision: `bd16603d8be2ca58de8eafde93f91cb18e79a4d3`;
prepared dependency revision:
`4f6fe9358eaf2a6274f152005578957335acd724`.
