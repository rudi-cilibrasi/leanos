# Physical Qotom PCI address readback mismatch

Clean source `a0af62aae53967bdf53a2ad7503cab4e8060461c` built the lab ELF
`864f2afdde737472ccb8c2966af0a9dcb7428dfee02a9fe8bf29ab5e8cd5229c`.
The legacy USB image passed eight native QEMU cases and five USB boot paths.
Before the trial, the USB serial identity, filesystem and six installed hashes
were verified. The link was FTDI/null modem to COM1, 38400 baud, 8N1,
no flow control, using the protected completion-recovery runner.

The instrument observed 6,618 reads and one CF8 mismatch, at the same read
that triggered the collector capacity guard:

| Field | Raw value | Decode |
| --- | --- | --- |
| Requested CF8 | `0x8018e900` | `18:1d.1`, offset `0x00` |
| Observed CF8 | `0x8000e86c` | `00:1d.0`, offset `0x6c` |
| Returned CFC value | `0x00082005` | Raw value, not a validated device identity |

The first recorded mismatch is also the last read. The requested address
matches the reported overflow BDF. Earlier complete native inventories identify
`00:1d.0` as the `8086:0f34` EHCI USB controller. This capture does not establish
which agent changed CF8, when during the sequence it changed, or that the CFC
value belongs to the address read back afterward. SMM/USB legacy interference
is a hypothesis. Matching CF8 on other reads cannot prove exclusive ownership.
The extra CF8 read changes timing compared with the uninstrumented scan.

The wrapper returns the original configuration value unchanged; it does not
retry, filter, repair, or admit it. CPU selection was 65536 and MSR readback 1.
The PCI collector emitted `FAIL reason=qotom-pci-enumeration`, published no
partial headers, and never reached ACPI capture or platform/CPL3 admission.

FreeBSD SSH returned, boot time changed from 1789103232 to
1789104190, and the one-shot request was consumed. Post-FINAL
quiet was 34.325 seconds. The result's historical
`hang_recovery=true` labels the protected scenario and does not prove watchdog
expiry; this was completed-run recovery, not an injected hang.

Serial SHA-256: `f0a9f0b95f79889745fe42bc2e49c5b90abde9d5d37f69bc2839ce07adc695ab`.
The original bytes, event timestamps, handoff, trace and replay/recovery records
are retained. No physical configuration data writes were introduced by the
read trace. A reviewed USB ownership/firmware contract remains future work.
