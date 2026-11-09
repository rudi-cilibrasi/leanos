# Deviations of the pci-capabilities project

The theorems are about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/caps_unit.c`)

`pci_collect_capabilities` and `pci_capability_finish` are `static inline`.
The unit includes `boot/pci-capabilities.h` unchanged and gives the walker the
external name `caps_collect`. The wrapper only forwards its arguments, and its
body is proved like every other function. The header's other include,
`boot/pci-enumeration.h`, is compiled too, but nothing in it is reached.

## D2. The device is the law's

The kernel passes a configuration-space reader: an ECAM or mechanism-#1 read
of real hardware, with the bus, device and function it names. Each law passes
its own reader instead:

- `capabilities_adversarial`: a device that may fail any read or answer any
  value, a different one each time;
- `capabilities_complete`: a fixed configuration space that always answers.

The walker's proof does not depend on either. It holds for every callback that
answers each read with success and a value, or with failure, and the laws
instantiate it (`CapsSpecs.read_spec`, parameterized by the device). The
kernel's own readers, their decoding of addresses and their behaviour on real
buses are outside these theorems.

## Not deviations, but limits of the laws

- The walker reads through the callback only; it cannot make the device's
  configuration space an atomic snapshot. Law 1 states what it publishes in
  terms of the answers it got, whatever the device does between reads.
- Partial correctness: termination is not claimed, though every loop is
  bounded (4 + 48 reads at most, which law 1 does state).
