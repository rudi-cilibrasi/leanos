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

Build the replay tool with `bash scripts/build-qotom-bsp-replay.sh ordinary`
and pass its path through `--bsp-replay` to the protected runner, alongside
`--native-kernel` and its prerequisite options. The runner pins executable and
decoder hashes before arming, rechecks them before classification, and retains
`native-bsp.json` with the original sample and result. Strict decoding binds
the unique record to the root-selected MADT from that same capture and compares
all six result words against generated replay. Missing/duplicate/misplaced
records, differing addresses/lengths, overflowing scalars and inconsistent
rejection terminals fail. Earlier CPU/firmware failures need no BSP record;
BSP failures retain their own terminal reason without claiming an ECAM fault.

Run `python3 scripts/test-qotom-native-bsp-capture.py` for synthetic matching,
rejecting and malformed records over retained physical firmware/recovery bytes.
The tests also run with the pinned sanitized replay, instrumenting both the
host parser/consumer and generated code. These records are synthetic, not a
physical BSP result. A physical capture is still required. The currently installed USB image
remains the earlier native PCI diagnostic. This build alone does not satisfy
issue #331's physical topology admission requirement.
