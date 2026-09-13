# Native Qotom graphics BME capture — 2026-09-12

A protected Win7 Legacy boot completed the bounded Valleyview graphics
bus-master transition at PCI `00:02.0` (inventory index 1). Before the write,
LeanOS refreshed the retained RCS, VCS and BCS observations. Both samples again
reported tail, head, start and control as zero and mode as `0x200`, so all three
rings remained stable, invalid/idle and empty. It then performed one 16-bit PCI
Command write from `0x0007` to `0x0003`, observed the exact readback, repeated
the complete ring sample, and checked Command once more. Memory and I/O decode
therefore remained enabled while Bus Master Enable was clear.

The native stage performed its bounded 127 PCI/MMIO reads and one word write
through consumed authorities tied to the exact boot header, quiet ring state,
firmware tables, active CR3 hierarchy and alias exclusions. The protected
runner independently decoded the record and retained the raw stream. This is a
successful Command transition with quiet ring evidence; it does not establish
graphics ownership, continuing firmware or AP exclusion, posted-write drain,
DMA quarantine, or platform/CPL3 admission. The terminal remains
`qotom-platform-pending`.

The retained `broadcom-status-rejection` attempt stopped safely before reaching
the graphics stage. Four root ports reported PCIe Device Status `0x0010`
instead of the earlier `0x0011`; only the sticky Correctable Error Detected bit
differed, and Transactions Pending was clear in both values. The Broadcom gate
reported status 12 without attempting a write. The corrected gate accepts the
exact pair `0x0010`/`0x0011` while continuing to reject every other status word.
The successful run exercised the mixed `0x0010`/`0x0011` root-port state before
continuing through Broadcom D3hot and graphics BME.

FreeBSD recovered automatically after 34.304877213027794 seconds of serial
quiet, boot time 1789244265 to 1789246000, with the one-shot request consumed.
Independent SSH verified USB serial 11758C40, the installed image and GRUB
hashes, rollback archive, `request=none`, no remaining USB mount, and the
recovered Intel graphics device with its apertures enabled in D0. Serial was
FTDI/null-modem COM1 at 38400 baud, 8N1, with no flow control.

ELF SHA256:
`7a5adf357d7bfd9d52839f84889e240680d2d1db7fdc43c0c4fcfdc5cbf638ca`.
Successful raw capture SHA256:
`4998a356f2daa79903d8d8c4a6242ce8ceec9ed88b68733318fb8834e65b6f34`.
Rejected raw capture SHA256:
`6db7ffc9898bbddaef448e670c106d2934a2b8c3e218bff43c1c7bcbbcef42ca`.
Build and runner revision: `d9a08d23f0a03224c219c637d70b1e62b2441a4d`.
The clean build manifest contains the dependency-chain hashes. Ordinary and
pinned sanitizer tests, the canonical image build, guarded USB install, FAT
check, protected physical runner, replay and recovery inspection passed.
