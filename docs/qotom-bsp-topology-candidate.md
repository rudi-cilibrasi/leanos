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

The candidate also has a generated-C replay boundary described below. No
production-kernel consumer is added here. Register read fidelity and
same-CPU temporal binding remain caller obligations; the captured lab runner
supplies evidence for one boot, not a general hardware proof. The BSP flag
also cannot establish the state of the other processors.

## Generated-C bootstrap boundary

`LeanOS.QotomBootstrapABI.query` / `leanos_qotom_bootstrap_query` takes the
actual handoff bytes, root address/bytes, ordered table addresses/bytes,
executing ID and bootstrap scalars. The existing captured-root adapter checks
its bounds and decoder envelope first. Its single-core policy result does not
authorize this candidate: the complete Qotom topology and BSP binding must
then pass separately. The existing captured-root ABI is unchanged.

The five result words are version, status, ID/error, processor count/detail,
and APIC-base/extra. Word 0 is version 1 and words beyond 4 are zero. Status 1
means a bound candidate with ID 0, four processors and APIC-base `0xfee00900`;
it never means platform or runtime admission. Status 2 preserves the existing
root-adapter rejection projection. Additional adapter errors 306, 307 and 308
reject overflowing CPUID, non-Boolean availability and overflowing sample ID;
309 rejects an inconsistent prior adapter/decode result. Executing-ID and
byte/table bounds retain their existing adapter codes.

Status 4 encodes Qotom topology errors in order: unsupported source (1),
version (2), excess processors (3), duplicate ID (4), no enabled processor (5),
wrong BSP (6), or differing inventory (7). Status 5 encodes bootstrap errors:
unavailable (1), missing features (2), sample ID mismatch (3), BSP flag clear
(4), or unsupported APIC state (5). Rejected bootstrap/topology results expose
no accepted processor count or register value.

`python3 scripts/qotom-bootstrap-corpus.py` writes the same 19 input bundles
and 114 expected words for Lean and C, including four scalar-boundary cases
in addition to the typed model's 15 cases. Run its generated
`build/qotom-bootstrap-corpus/Replay.lean` with `lake env lean`, and run
`scripts/check-qotom-bootstrap-host.sh ordinary` followed by `sanitized` for
independent C execution. The runner uses the shared hosted-boundary compiler,
full sanitizer module closure, export-entry coverage and output comparison.

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
