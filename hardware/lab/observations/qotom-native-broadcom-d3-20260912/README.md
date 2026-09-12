# Native Broadcom D3hot capture — 2026-09-12

The protected Win7 Legacy boot completed the bounded Broadcom BCM43224
transition at PCI `02:00.0` (inventory index 14). LeanOS read Command `0006`,
wrote and read back `0000`, then obtained two PCIe Transactions Pending-clear
samples separated by the bound 10 ms ACPI PM-timer delay. Device Status was
`0019`. It required PMCSR `4008`, wrote `400b`, and read back D3hot with PME
disabled and the complete four-entry capability list unchanged.

The [design](../../../../docs/qotom-broadcom-d3.md) binds the endpoint and its
bus-2 root port to the copied firmware tables, active ECAM root, retained PCIe
state, successful root-port BME clear, and two earlier root-port pending-clear
samples. A protected window permits exactly two ordered 16-bit configuration
writes and revokes authority on every rejection or reported failure.

This is configuration-visible evidence for the bounded Command-off and D3hot
transition. It does not establish that Broadcom firmware or internal engines
were stopped, posted writes completed, firmware and APs remained excluded, or
the whole machine reached DMA quarantine. The terminal remains
`qotom-platform-pending`.

FreeBSD recovered automatically after 34.32607858401025 seconds of serial
quiet, boot time 1789199756 to 1789201482, with the request consumed.
Independent SSH verified the installed hashes, backup, `request=none`, no
remaining USB mount, and the recovered Broadcom state at Command `0006` and
PMCSR `4008`. Serial: FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`255546caf21a680b1114817f1874e3d08c5d3e8e524155ddfae38b64bab94110`.
Raw capture SHA256:
`fa0eb74f81f896f7594551236501ddcca5cc17e5738d06f15cd004cc854a45a2`.
Build and runner revision: `9a0f83fd83314f90bb83b570fc6b86121b73f1ef`.
The clean build manifest contains the complete dependency-chain hashes. The
ordinary and pinned sanitizer capability suite, focused protected projection,
guarded USB install, FAT check, read-only verification, physical runner, and
independent recovery inspection passed.
