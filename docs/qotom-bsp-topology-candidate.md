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
reconstruction, not a captured Legacy GRUB handoff.

## Remaining admission requirements

This witness grants no runtime authority. It is not a complete platform profile,
a memory-allocation witness, or a proof that the other processors are dormant.
The kernel does not call this candidate policy. Before physical admission,
issues #291 and #331 still require explicit firmware/reset/SMM/hotplug assumptions,
executing-CPU observation binding, modeled runtime AP-start rejection,
final-object AP-start exclusion, full platform composition and a physical
capture. The captured unusual MADT local-APIC NMI routing bytes are retained
and remain unchecked by the topology decoder. Interrupt routing safety must
be resolved separately before granting runtime authority.
