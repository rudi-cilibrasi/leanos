# J1900 entry-policy review (#328)

## Measured input

The read-only [CPUID producer](../hardware/lab/capture-cpuid.c) was compiled on
FreeBSD and run under `cpuset -l 0`, 1, 2 and 3. The [raw leaves and provenance](../hardware/cpu-corpus/qotom-j1900-20260909/provenance.json)
retain each CPU separately. All report signature 00030678 (family 6, model 55,
stepping 8), basic maximum leaf 0000000b, and extended maximum 80000008. Initial
APIC IDs are 0, 2, 4 and 6, matching the earlier MADT inventory.

MSR, PAE, SEP, SYSCALL, long mode, NX and SMEP are advertised. XSAVE, AVX and SMAP
are absent. Leaf 0D was not queried because it exceeds the advertised basic
maximum. The raw logical-address capacity in leaf 1 must not be substituted
for the enabled processor count; topology authority remains issue #331.

These are FreeBSD CPUID observations, not a LeanOS admission or CPL3 capture.
No MSR, control register, boot environment or USB content was changed.

## Architecture source checked

Intel SDM Volume 2B, order 253667-060US, September 2016, is available from
[Intel](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf).
Its SYSCALL operation and 64-bit exception table (printed pages 4-668–4-669)
reject disabled EFER.SCE with #UD before loading the alternate target. Its
SYSENTER operation (4-671) rejects a zero IA32_SYSENTER_CS selector with #GP(0)
before changing the stack or target; the 64-bit exception table (4-672) retains
that rule. Thus the intended Intel denial vectors are 6 and 13 respectively.
This review does not yet establish the complete J1900 MSR inventory, especially
whether the AMD-oriented CSTAR access is architecturally authorized.

The current [Intel Volume 4](https://cdrdv2-public.intel.com/922493/335592-092-sdm-vol-4.pdf),
335592-092US (June 2026), section 2.4 includes model 06_37H. Table 2-6
lists SYSENTER_CS/ESP/EIP (2-125–126), EFER, STAR, LSTAR and FMASK (2-133),
but omits CSTAR. The architectural table 2-2 (2-93) nevertheless lists CSTAR
as read/write when extended-leaf EDX bit 29 is set, while describing it as
unused. This discrepancy does not establish that CSTAR faults on J1900.
The implementation review must distinguish architectural access from useful
denial state; do not infer either a required CSTAR write or its absence solely
from the model table. No MSR probe has been run on the physical machine.

## Current code audit and required changes

`PrivilegeEntryControl.expectedVector` already distinguishes Intel SYSENTER,
but `Accepted`/`validate` select only the AMD contract. The generic `enabled`
view now recognizes Intel SYSENTER in long mode and tests selector bits 15:2,
so RPL-only or upper-register bits cannot make a null selector usable. The
existing AMD long-mode denial remains intact, and unsupported vendors do not
enable SYSENTER. Intel's [SDM Volume 3A, section 5.8.7.1](https://cdrdv2-public.intel.com/819714/253668-sdm-vol-3a.pdf)
documents the Intel 64-bit path; [Volume 2, SYSENTER](https://cdrdv2-public.intel.com/671110/325383-sdm-vol-2abcd.pdf)
specifies the null-selector check. This finite enablement view does not prove
instruction execution or relax `Accepted`. The selected extended-feature projection includes
XSAVE and AVX; those cannot be asserted for these measured J1900 leaves.

`boot/boot.S` writes EFER, STAR, LSTAR, CSTAR, FMASK and all three SYSENTER MSRs
in the 32-bit normalization path. A new early gate now checks Intel/AMD vendor
words, basic/extended leaf availability, the required legacy feature mask,
and SYSCALL/NX/long-mode support before any CR/MSR access. It follows the first
kernel-owned IDT publication and preservation of the Multiboot registers.
This establishes common architectural prerequisites, not the exact J1900
profile or permission to enter CPL3. `check_fast_entry_cpuid` still runs later
in C and remains AMD-only; the full raw J1900 selector still needs wiring there.

The separate early rejection emits `FINAL status=FAIL reason=early-cpu-capability`
when UART readiness permits. Each byte has at most 65536 readiness polls; a
timeout abandons output and halts. This path does not reuse the unbounded
`EARLY_SERIAL32` loop used by the older exception stubs. The linked-instruction
checker verifies the guard, handoff preservation, control-access ordering,
retry decrement and terminal path. Five altered ELF cases cover weakened MSR/NX
masks, guard bypass, zero retry budget, and a non-decrementing poll loop. The
two new port sites are declared in each image's reviewed I/O inventory.
The port audit now decodes the complete bootstrap interval in 32-bit mode:
decoding its far jump as 64-bit code had falsely interpreted address bytes as
port instructions. A separate injected real I/O instruction is still rejected.
Run `scripts/test-early-cpu-image.sh ISO` for the focused QEMU `msr=off` and
`nx=off` rejection fixtures. They require exactly the early failure record and
a terminal timeout; they do not count as canonical q35 admission evidence.

The next implementation needs a closed, versioned raw-leaf projection, exact
profile/control readback checks, generated profile-bound records, Lean/C
agreement and malformed/mixed-profile negatives. An Intel execution fixture
must exercise the two denial outcomes. Absent SMAP remains a distinct #329
policy dependency; this issue must not silently authorize production CPL3.

## Initial checked projection

`LeanOS/J1900CpuProfile.lean` now selects the measured version-one capability
projection from five raw CPUID slots with explicit presence bits. It rejects
wrong versions, missing/extra presence bits, insufficient leaf ranges, wrong
vendor/signature, missing required legacy/extended features, absent SMEP,
unexpected XSAVE/OSXSAVE/AVX, and unexpected SMAP. It does not infer active
long mode from support bits or authorize production CPL3.

Theorems connect successful selection to all checks and the required raw feature
masks, and establish that the result leaves CPL3 unauthorized. Run
`python3 scripts/test-j1900-cpu-profile.py` to verify capture hashes and replay
four measured CPUs plus 29 altered snapshots using kernel-checked Lean reduction.
The same runner checks 162 fast-entry combinations across vendor, execution
mode, feature exposure, and null/non-null selectors (including RPL and upper
bits), also by kernel reduction. These are model checks, not hardware execution.
The `leanos_j1900_cpu_select` export accepts 22 unsigned 64-bit words: version,
presence, and EAX/EBX/ECX/EDX for each of the five slots in order. It rejects
any input exceeding 32 bits before narrowing, including unused register words.
Results 1–11 identify selection rejections, 12 identifies an input-width
violation, and 0x10000 selects the existing capability projection. That result
does not authorize MSR accesses or production CPL3. Each call supplies a whole
snapshot; the boundary stores no intermediate state between calls.

The runner also checks 55 raw-boundary cases in Lean and generated C: the
33 snapshots above and a high-bit mutation of each of the 22 input words.
`scripts/check-j1900-cpu-host.sh` connects that corpus to the shared hosted
boundary runner, including its instrumented export coverage and sanitizer mode.
The selector, rejection mapping, and masks are inlined so the generated scalar
entry point does not construct boxed snapshots or invoke lazy initialization.
The focused runner also links only this function and its reachable dependencies
into a standalone ELF without runtime libraries and requires no undefined
symbols. This establishes link independence for that artifact, not an early
boot execution or stack/memory admission proof.

The default Lean root imports this module, its three theorems are in the
checked invariant inventory, and `scripts/check.sh` runs these capture and
fast-entry cases. The boot adapter and completion of the MSR policy remain
required for #328; hosted replay is not a physical CPU admission capture.

## CPU and control binding

`J1900EntryControl` combines the raw capability selector with an exact modeled
control tuple: Intel long mode, completed writes and readback, disabled fast
entry targets, and the measured extended features without XSAVE/AVX. Its three
proofs connect executable validation to that tuple, disabled SYSCALL/SYSENTER,
and completed initialization/readback observations. It is separate from the
existing production return gate and does not establish the no-SMAP policy.

The focused runner checks 51 CPU/control combinations, including mixed AMD/Intel
data, incomplete observations, every modeled EFER bit and target register, plus
the Intel vectors 6 and 13. These new binding checks currently run in Lean;
the generated-C control adapter and physical readback remain to be connected.

Local execution at the early-gate revision passed canonical blocking IPC and
both AMD fast-entry probes under TCG. KVM on mgnuc's Intel i7-10710U passed the
canonical and SYSCALL probes, but SYSENTER reported vector 13 where the guest
contract expected 6; QEMU exited 39. The configured guest vendor was
`AuthenticAMD`. [The failed serial trace and provenance](../hardware/lab/observations/mgnuc-kvm-sysenter-20260909/provenance.json)
are retained. This demonstrates a mismatch in that tested configuration;
an unchanged-main baseline was not run, so it does not establish when the
mismatch was introduced. Intel-specific execution testing must account for
the actual instruction behavior rather than relying on a vendor-string override.
