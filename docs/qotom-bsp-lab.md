# Native BSP lab integration

The recovery image builder's `--bsp-topology` option requires the existing
`--native-inventory` chain of ACPI, bootstrap, DSDT and ECAM options. Its output
is isolated in `build/qotom-bsp-lab`; it does not replace the previously built
native PCI lab ELF or install anything on USB.

After all root-selected tables have been copied and their capture emitted,
the lab retains the actual copy count. The exact-firmware ECAM gate runs
first. The BSP caller then selects the unique MADT from those copies and
runs the existing generated envelope validator over its complete bytes.
Only that validated entry span reaches the bounded BSP consumer.

The caller samples the executing APIC ID, then performs a fresh CPUID leaf-1
read and gates IA32_APIC_BASE access on its MSR/APIC feature bits. Its
`NATIVE-BSP` record includes this new observation, the selected MADT address
and length, and the consumer's actual status/detail/offset and bound values.
Replay must use this observation rather than substitute the earlier bootstrap
sample or the expected platform constants. Same-CPU read fidelity and firmware
behavior remain explicit hardware assumptions.

The generated object retains only the two scalar exports and permitted
internal helpers. The image builder links it at both image stages, refreshes
the ABI header, verifies identical page plans, checks the Multiboot2 ELF and
records source/generated-C/object hashes in the build manifest. The canonical
kernel source and q35 admission path are unchanged.

A candidate failure stops with `qotom-native-bsp`; a match proceeds through the
existing inventory check to `qotom-platform-pending`. This is not allocation
or platform publication, AP-dormancy evidence, NMI routing admission or CPL3
entry. Exact foreign firmware rejection still occurs before this new check.

Strict protected-runner decoding of `NATIVE-BSP` and a physical capture are
still required before deploying this image. The currently installed USB image
remains the earlier native PCI diagnostic. This build alone does not satisfy
issue #331's physical topology admission requirement.
