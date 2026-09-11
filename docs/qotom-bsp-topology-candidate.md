# Qotom BSP topology candidate

`LeanOS.QotomBspTopology` checks the processor observation needed by #331.
Its witness binds the entire snapshot to ACPI MADT snapshot version 1,
recorded and executing BSP ID 0, and the ordered processor IDs 0, 2, 4, 6.
All four records must be enabled and none may be online-capable. Changed
order, extra or missing records, changed flags, and changed identities fail.
The exact inventory comes from the retained Qotom capture; the policy does
not learn a baseline at runtime.

The witness contains the original snapshot and a proof of equality with
that complete baseline. Acceptance preserves the caller's observation.
General theorems bind both BSP identities, enumerate the four enabled
processors, and establish that the existing single-core policy still rejects
this same witness with `multipleEnabledProcessors`.

`checkAuthoritative` consumes the existing root-selected snapshot decoder.
It preserves ACPI errors before applying processor policy. It does not accept
a caller-supplied MADT as a substitute for the selected root and table copies.

## Validation

Run `lake build LeanOS` for the policy proofs, inventory negatives and eight
synthetic authoritative-path fixtures. Run
`python3 scripts/test-qotom-bsp-capture.py` after building for eight cases
using the retained FreeBSD UEFI capture. The latter first validates the corpus
manifest hashes and the FreeBSD source projection, then uses the existing
converter and mutation producer. It writes its Lean replay to
`build/qotom-bsp-capture/Replay.lean`.

The captured baseline passes this topology candidate. Duplicate CPUs, no CPUs,
wrong BSP, corrupted MADT checksum, corrupted root checksum, incorrect root
length and incorrect root address produce the specified typed rejections.
Derived checksum repairs are confined to the existing mutation producer;
raw captured inputs are never repaired. This is a FreeBSD-derived UEFI
reconstruction. `--native` instead checks the retained actual Legacy GRUB
handoff and its root-selected ACPI table copies, without reconstructing either.

## Architectural BSP binding

`checkBootstrapAuthoritative` first obtains the existing authoritative topology
witness, then binds an additional `BootstrapObservation` to its executing ID.
It requires an available read, CPUID MSR/APIC feature bits, and the complete
captured IA32_APIC_BASE value `0xfee00900`. This fixes the APIC base and mode
as well as requiring the architectural BSP bit. Other CPU capability bits
remain the separate J1900 CPU profile's responsibility.

The dependent witness retains the original observation and its relationship
to the original topology witness. General proofs establish preservation of
that observation, exact acceptance conditions, required feature bits, the BSP
flag, and executing identity 0. The combined witness still receives the
existing q35 single-core policy's `multipleEnabledProcessors` rejection.

After `lake build LeanOS.QotomBspTopology`, run
`python3 scripts/test-qotom-bootstrap-binding.py`. It verifies the retained
[physical bootstrap capture](../hardware/lab/observations/qotom-bootstrap-20260911/README.md),
extracts both observations from the same serial capture, and checks 15 Lean
cases. They include unavailable reads, absent feature bits, mismatching sample
or executing IDs, a clear BSP flag, disabled APIC, x2APIC mode, changed APIC
base, reserved bits, duplicate/missing CPUs and root/MADT checksum errors.
Original bytes are preserved; only named negative-case fields are mutated.

This is hosted Lean candidate validation. No independent generated-C binding
ABI or production-kernel consumer is added here. Register read fidelity and
same-CPU temporal binding remain caller obligations; the captured lab runner
supplies evidence for one boot, not a general hardware proof. The BSP flag
also cannot establish the state of the other processors.

## Remaining admission requirements

This witness grants no runtime authority. It is not a complete platform profile,
a memory-allocation witness, or a proof that the other processors are dormant.
The kernel does not call this candidate policy. Before physical admission,
issues #291 and #331 still require explicit firmware/reset/SMM/hotplug assumptions,
runtime integration of the bound executing-CPU observation, modeled AP-start rejection,
final-object AP-start exclusion, full platform composition and a physical
capture. The captured unusual MADT local-APIC NMI routing bytes are retained
and remain unchecked by the topology decoder. Interrupt routing safety must
be resolved separately before granting runtime authority.
