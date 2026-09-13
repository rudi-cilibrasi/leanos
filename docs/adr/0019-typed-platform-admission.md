# ADR 0019: Typed platform admission profiles

## Status

Accepted for the pinned q35 construction and the Qotom J1900 CLBTM210
reference machine.

## Decision

Every CPL3 boot selects one complete, versioned platform manifest through the
closed `PlatformProfileId` vocabulary. The accepted identifiers are `q35-v1`
and `qotom-j1900-clbtm210-v2`. The earlier
`qotom-j1900-clbtm210-v1` hardware row remains a controlled rejection and is
never reclassified.

Selection consumes the profile code and version together with identities and
acceptance results for the firmware root, bounded memory map, complete PCI
contract, UART, BSP topology, isolation strategy, supported-facility policy,
bounded scenario, and terminal policy. Every value must match the single
selected manifest. Unknown identifiers, wrong versions, and field mixtures
return stable typed reasons before CPL3.

The q35 manifest preserves the existing fixed firmware, memory, PCI, topology,
SMAP, VT-d, and assigned-EDU meanings. Its successful serial transcript is
unchanged. `isa-debug-exit` remains useful to the QEMU runner, while the
platform-independent terminal event is the versioned serial `FINAL` record
followed by an absorbing halt.

The physical profile binds the reviewed XSDT/MADT and Multiboot2 shapes, the
sixteen-function final PCI state and trust contract, COM1 at 38400 8N1,
executing APIC ID zero among four advertised processors, the no-SMAP copy-root
strategy, and the bounded two-subject blocking-IPC scenario. VT-d and the
assigned-EDU family are `not-applicable` with reasons in the manifest; their
absence is not counted as passing containment evidence.

## BSP-only execution

The Qotom profile admits only the executing BSP. It trusts the firmware and
reset-time state to leave the other advertised processors dormant. LeanOS does
not publish or invoke an INIT, SIPI, trampoline, hotplug, or other AP-start
operation in this construction. The closed runtime vocabulary includes an AP
start so that any such attempt enters a typed absorbing halt while preserving
the admitted profile and leaving `apStartIssued` false. Final-object audits
independently reject an AP trampoline or reachable start path.

This is BSP-only admission, not SMP support. The residual trust boundary
includes firmware MADT truth, reset-time AP behavior, executing-APIC-ID
sampling, SMM/SMI, hotplug absence, and mechanisms outside the modeled
operation vocabulary.

## Evidence and release binding

`hardware/platform-profiles.json` is the closed registry. It pins both profile
files by SHA256. Release packaging validates that registry and ships it with
both manifests, adding all three files to `SHA256SUMS`. A release consumer can
therefore bind an image's profile identifier to the exact reviewed manifest.

The Qotom boot emits `PLATFORM-ADMISSION` with
`qotom-j1900-clbtm210-v2` before its existing blocking-IPC readiness and CPL3
records. The retained physical evidence bundle records that identifier, source and
ELF digests, the complete decoded observation, serial transcript, semantic
terminal, watchdog recovery, and the two non-applicable scenario families.

## Trust and exclusions

The Lean theorem proves selection uniqueness, complete-field matching,
profile preservation, and absence of AP-start publication for the modeled
runtime. Hosted generated-C checks cover both accepted profiles and controlled
mismatches. These results do not prove that C supplied faithful hardware
observations, PCI or ACPI semantics, page-table and entry instructions,
compiler or linker refinement, firmware/SMM behavior, CPU or chipset behavior,
serial delivery, watchdog recovery, timing, or general PC compatibility.

Any firmware-table, memory-map, PCI identity/control, UART, executing-BSP,
isolation, facility, scenario, or terminal change requires a new profile
version and fresh hardware evidence. Runtime learning, fuzzy matching, and
field-by-field fallback remain prohibited.
