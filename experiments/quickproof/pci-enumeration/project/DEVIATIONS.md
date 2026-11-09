# Deviations of the pci-enumeration project

The theorem is about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/enum_unit.c`)

`pci_enumerate_segment` is `static` and `pci_enumeration_finish` is `static
inline`. The unit includes `boot/pci-enumeration.h` unchanged and gives the
scan the external name `enum_scan`. The wrapper only forwards its arguments,
and its body is proved like every other function.

## D2. The device is the law's

The kernel passes a configuration-space reader: mechanism #1 on the Qotom
(`boot/pci-config-read.h`) or the ECAM reader of the lab images
(`boot/qotom-ecam-read.h`). The law passes its own reader instead: a device
that may fail any read or answer any value, a different one each time, and
that checks every read against the order the law states.

The scan's proof does not depend on that device. It holds for every callback
that answers each read with success and a value, or with failure, and the
law instantiates it (`EnumSpecs.read_spec`, parameterized by the device). The
specification only asks the callback for the scan's next read. The kernel's
own readers, their decoding of addresses and their behaviour on real buses
are outside this theorem.

## Not deviations, but limits of the law

- The scan reads through the callback only; it cannot make the segment an
  atomic snapshot. The law states what the scan publishes in terms of the
  answers it got, whatever the device does between reads.
- Partial correctness: termination is not claimed, though every loop is
  bounded (at most 65536 + 16 * 15 reads, which the law does state).
