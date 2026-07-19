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
The boot assembly now realizes the modeled MSR recipe before entering long
mode. After the shared vector-6/7 exception gates and TSS are installed,
`check_fast_entry_cpuid` first requires the exact `AuthenticAMD` vendor string,
basic CPUID leaf 1 with SEP/SYSENTER advertised, and extended leaf `0x80000001`
with SYSCALL and long mode advertised. `check_fast_entry_control` then rereads
the complete modeled MSR tuple before the first CPL3 return. It compares EFER
through the explicit SCE/LME/LMA/NXE mask and requires exact zero values for
every target register. Controlled source fixtures reject an omitted CPUID
check, vendor drift, and long-mode feature drift. These are checked machine
behaviors under the pinned QEMU contract, not proof that hardware implements
the model or the cited instruction semantics.

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
SYSENTER attempts both require vector 6 (`#UD`). Dedicated images execute each
raw two-byte opcode at the single allowlisted CPL3 probe site. Both exceptions
cross the shared vector-6 normalizer, bind the hardware frame to the protected
current subject/CR3/ordinary entry stack, and invoke the fixed-width privilege
entry classifier. A typed denial then reuses the authoritative cleanup and
fresh-peer selection boundary: subject A is removed, subject B's kernel-owned
context is restored under root B, and B reaches CPL3 only through the sole
validated `iretq` epilogue.
A kernel-origin event, stale live controls, unexpected vector or error shape,
ordinary `int 0x80` relabeled as denial, alternate CPL0 target execution,
user-owned entry stack, or stale subject/address-space/CR3 binding becomes a
typed fatal result. `denied_subject_confined` proves that a contained event can
name only the authoritative current subject. The completed
`ResumablePreemption.cleanupSubject` theorem is re-exposed to show that cleanup
cannot retain that subject as live, queued, current, or resumable.

`armUserReturn` rejects unless the recorded and live tuple are identical and
accepted. The machine return validator now rereads the complete MSR denial
tuple at every use of the sole outbound gate, after validating the extended
controls and immediately before the existing entry latch is consumed. The
composite wrapper applies the same prefix to every
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

The final-ELF policy requires the eight reviewed writes, nine reviewed reads,
their labeled sites, and no SYSCALL, SYSENTER, SYSRET, or SYSEXIT opcode in
production images. Each deliberate probe image contains exactly one expected
SYSCALL or SYSENTER instruction at the exported probe label and rejects every
other fast-entry opcode. Controlled fixtures reject inherited SCE, an omitted
boot or return-gate readback, and an extra MSR write. The two QEMU scenarios
record the CPU/MSR snapshot, raw vector-6 denial, unreachable alternate target,
complete attacker cleanup, validated peer return, survivor canaries, exact
serial transcript, command, image, ELF, and hashes as tested evidence.

The repository-owned runner fixtures reject a missing entry manifest or control
snapshot, wrong vector/error shape, stale binding, unexpected target execution,
policy relaxation, attacker-selected survivor, kernel-origin containment,
direct handler entry, partial or reordered output, reset, triple fault, and
hang. Each successful probe also preserves a three-record CPU/CPUID/MSR/control
snapshot beside the exact serial log. The remaining machine checkpoints are
additional controlled build/guest mutations and the final global-invariant
composition requested by follow-on #104. Those
results must be labeled checked/tested evidence, not Lean proof.
