# Native inventory lab image

The recovery-lab builder accepts `--native-inventory` only with `--ecam-read`
and its existing firmware, DSDT, memory and bootstrap capture prerequisites.
It links the proved scalar export into both the prelink and final image, checks
page-plan equality, refreshes the generated ABI header, and records the native
object, generated C, Lean sources and helper hashes in the build manifest.
The native object uses general registers only, has no Lean runtime dependencies
or writable state, and is retained from the stable scalar export.

After a completed ECAM scan and raw-header output, the image validates that
private snapshot and emits:

```text
LEANOS-LAB/1 NATIVE-PCI profile=qotom-native-ecam-v1 status=0 index=0 count=16
```

Status zero matches the inventory. Status three rejects the count; status four
rejects the header at the reported index. Rejection terminates with
`qotom-native-inventory`. A match still terminates with `qotom-platform-pending`;
no device writes, DMA authority or CPL3 admission are enabled. Earlier CPU,
firmware or scan failures do not produce an inventory result.

Offline and protected capture replay select `--native-inventory --native-kernel`
and the native inventory replay executable. The kernel flag requires the native
profile; the protected runner additionally requires ECAM and records the kernel
selection among its checked replay inputs. The kernel record must match the
independent generated array checker exactly, including status, index and count.
A missing, duplicate, misplaced or inconsistent record rejects. The original
capture hash includes the kernel record; the default offline interpretation is
unchanged.

Local validation built the actual native-checking ELF and verified every build
manifest hash, the stable linked export, no unresolved ELF symbols, and matching
prelink/final page plans. QEMU with foreign q35 firmware still rejected at the
ECAM arm gate before enumeration, with independent QMP ACPI-byte comparison.
Six capture tests use synthetic kernel records over the retained physical PCI
headers; they cover successful protected replay, explicit selection, malformed
or mismatched records, indexed identity failure, missing-function count failure
and incomplete scans. They are not a new physical Qotom capture.

The subsequent [physical Qotom capture](../hardware/lab/observations/qotom-native-inventory-20260911/README.md)
reported a sixteen-function native match. Independent replay agreed, and the
protected runner verified automatic recovery to FreeBSD and consumed request.
The retained physical capture is replayed by a seventh test with all bundle
hashes checked. Platform admission and device policy remain unfinished.
