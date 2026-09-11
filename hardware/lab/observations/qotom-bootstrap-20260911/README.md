# Qotom bootstrap-processor capture

Protected Win7 Legacy USB boot on Qotom J1900 / AMI CLBTM210, captured
2026-09-11 UTC from local mgnuc over FTDI/null-modem/COM1, 38400 8N1.
The lab image was built from clean source
`57d5b9f5805d21585c9a1de8b0d4cbf78c23aaa7`, with SHA256
`3c2b5d25fe50e3bfcca7d065a87903ff37eba1c78fed9e52c7606ee87c44684e`.
The opt-in bootstrap, handoff, ACPI and PCI read-trace flags were enabled.
All eight QEMU cases and 23 USB boot/recovery cases passed before installation.

The raw bootstrap sample is CPUID.1:EDX `3219913727`, available `1`, and
IA32_APIC_BASE `4276095232` (`0xfee00900`). BSP bit 8 and APIC enable bit 11
are set; x2APIC bit 10 is clear. The handoff independently reports initial
APIC ID 0. This observes the executing BSP, not the dormancy of other APs.
No APIC/MSR write or AP startup was added by the observer.

The original Multiboot2 block is 2,680 bytes at physical address 2,732,304,
with 19 memory entries. The root-selected XSDT and ten children were copied
before PCI enumeration: 11 tables totaling 3,951 bytes, all identical to the
preceding native ACPI capture. Neither the firmware nor handoff was repaired.

PCI enumeration stopped at its existing capacity guard, status 2, count 0,
reported address `3d:12.3`. The observer saw one CF8 mismatch over 16,004 reads:
requested `0x803d9300`, observed `0x8000e86c` (EHCI `00:1d.0`, offset `0x6c`),
returned value `0x00082005`. This does not identify the interfering agent,
establish the provenance of that CFC value, or demonstrate a real device at
the reported scan address. No partial PCI inventory was published.
The terminal reason remains `qotom-pci-enumeration`; no platform or CPL3
admission occurred.

The runner verified automatic FreeBSD SSH recovery, boot time
`1789104740` to `1789108214`, and a consumed one-shot request. The interval
from terminal output to recovery serial output was approximately 34.310 s.
This is reset-and-loader recovery evidence, not canonical halt evidence.
Original serial bytes, timestamped events, raw handoff, ACPI table bytes,
bootstrap metadata, generated CPU/PCI replay, source/image hashes and
recovery reports are retained without reconstruction.

Raw serial SHA256:
`a1bc53f6e1f9d2d37a32370e57c4960aade602202548e168ffb83fbcf494d7b5`.

BSP runtime admission, AP dormancy assumptions, final-object AP-start
exclusion, interrupt routing and DMA/PCI ownership remain separate work.
