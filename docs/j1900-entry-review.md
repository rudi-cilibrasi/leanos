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

## Current code audit and required changes

`PrivilegeEntryControl.expectedVector` already distinguishes Intel SYSENTER,
but `Accepted`/`validate` select only the AMD contract. Its generic `enabled`
view suppresses SYSENTER in every long-mode contract, which must be revisited
when Intel is admitted. The selected extended-feature projection includes
XSAVE and AVX; those cannot be asserted for these measured J1900 leaves.

`boot/boot.S` writes EFER, STAR, LSTAR, CSTAR, FMASK and all three SYSENTER MSRs
in the 32-bit normalization path. `check_fast_entry_cpuid` executes later in C.
A new profile must authorize operations before they execute, not merely relax
that late vendor comparison. Review the per-model MSR table and early CPUID
checks before deciding which accesses to omit or retain.

The next implementation needs a closed, versioned raw-leaf projection, exact
profile/control readback checks, generated profile-bound records, Lean/C
agreement and malformed/mixed-profile negatives. An Intel execution fixture
must exercise the two denial outcomes. Absent SMAP remains a distinct #329
policy dependency; this issue must not silently authorize production CPL3.
