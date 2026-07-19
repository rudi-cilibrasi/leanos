# Fast privilege-entry control model

`LeanOS.PrivilegeEntryControl` defines the finite Phase 2 policy that admits
`int 0x80` as the only modeled CPL3-to-kernel system-call mechanism. It is a
machine-entry authorization model, not another logical syscall ABI. The model
composes the completed inbound entry, guarded ordinary-stack, user-return,
fail-stop, cleanup, and extended-state contracts without claiming that the
compiled image implements them.

## Selected contract and denial recipe

The first accepted control tuple names the AMD vendor string and 64-bit mode
used by the repository's reviewed QEMU `-cpu max` configuration. It requires
the advertised SYSCALL and legacy SYSENTER feature projections, the existing
extended-state denial predicate, and the installed `int 0x80` manifest entry.
This is a finite repository contract, not a theorem about arbitrary AMD CPUs or
future QEMU versions.

The modeled kernel recipe preserves EFER.LME, LMA, and NXE; clears EFER.SCE;
zeros STAR, LSTAR, CSTAR, and SFMASK; and zeros the three SYSENTER MSRs. Both
the complete write sequence and an exact read-back comparison must be recorded.
An inherited zero value without those kernel-owned facts is rejected. Setting
SCE, changing any fast-entry target or mask, omitting a write, or observing a
read-back mismatch also rejects before user return.

The architectural assumptions come from the AMD64 Architecture Programmer's
Manual: SYSCALL with EFER.SCE clear raises `#UD`, and SYSENTER/SYSEXIT are
invalid in 64-bit mode and raise `#UD`. The zero SYSENTER tuple remains part of
the exact policy so a stale legacy-mode target cannot be accepted if the mode
contract changes. See the
[AMD64 system-programming manual](https://docs.amd.com/v/u/en-US/24593_3.44_APM_Vol2)
and the [QEMU system-emulation documentation](https://www.qemu.org/docs/master/system/introduction.html).
The machine stage must pin and retain the exact QEMU version, command, CPUID
projection, and MSR snapshot; documentation does not replace that evidence.

`enabled` gives the finite authorization view. The
`accepted_exactly_int80` theorem proves that, for every accepted control state,
it returns true exactly for `int80` and false for `syscall` and `sysenter`.
`validate_accepted_iff`, `validate_total`, and `validate_deterministic` connect
the executable validator to the proposition and establish a total,
deterministic decision.

## Denial, context binding, and fatal separation

`classify` accepts a contained denial only for a normalized user event with the
reviewed mechanism/vector pair, zero error code, the fresh live control tuple,
the guarded ordinary-entry stack identity, and the kernel-owned current
subject/address-space/CR3 binding. Opcode bytes and saved registers are absent
from its authorization input; `attacker_payload_erasure` proves arbitrary
scalar payload words cannot change the result.

For the selected AMD long-mode contract, representative raw SYSCALL and
SYSENTER attempts both require vector 6 (`#UD`). The model does not yet claim
that the image has installed and exercised that shared gate for this policy.
A kernel-origin event, stale live controls, unexpected vector or error shape,
ordinary `int 0x80` relabeled as denial, alternate CPL0 target execution,
user-owned entry stack, or stale subject/address-space/CR3 binding becomes a
typed fatal result. `denied_subject_confined` proves that a contained event can
name only the authoritative current subject. The completed
`ResumablePreemption.cleanupSubject` theorem is re-exposed to show that cleanup
cannot retain that subject as live, queued, current, or resumable.

`armUserReturn` rejects unless the recorded and live tuple are identical and
accepted. The composite wrapper applies the same prefix to every
`FailStop.Operation`; operations cannot carry or rewrite the controls.
`runComposite_preserves_policy` proves the exact policy survives every finite
nonfatal authoritative operation sequence, while mismatch is latched before
the underlying composite transition. The local classifier's halted state is
absorbing.

## Proof and evidence boundary

The stable claim is limited to the finite model: an accepted control tuple
enables exactly the reviewed manifest-backed `int 0x80` mechanism. The model
does not prove CPUID/MSR reads or writes, reserved-bit masks, instruction
decoding or exception priority/delivery, IDT/TSS loads, assembly cleanup,
generated C, compiler/linker output, QEMU/TCG, firmware/GRUB state, hardware,
or final-binary refinement.

The remaining machine checkpoint must normalize and reread the real MSRs;
extend the shared inbound manifest only for the exact denial gate; route denial
through authoritative termination and peer restore; gate the sole `iretq`
epilogue on the live tuple; add the fixed-width shared-oracle adapter; inventory
all MSR and fast-entry opcodes; and add raw SYSCALL/SYSENTER QEMU peer-survival
scenarios plus controlled build, guest, and runner negatives. Those results
must be labeled checked/tested evidence, not Lean proof.
