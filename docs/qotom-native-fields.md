# Scalar native PCI inventory comparison

`QotomNativePCIFields.checkHeader` takes an index, BDF and sixteen raw dwords.
It validates the header through the proved scalar decoder, then compares all
twelve identity/routing fields to the indexed native baseline row. Its theorem
returns a decoder result for those exact supplied words and establishes that
result's typed projection at the baseline index.

The scalar table is independently proved equal to all sixteen rows of the
existing typed native inventory. The twelve-field encoding is injective, and
complete encoded-list equality implies the whole native inventory property.
These results preserve ordering and count rather than allowing a union of
historical and native firmware observations.

`scripts/check-qotom-native-fields.sh` builds the module and retains the scalar
functions together with the scalar header decoder. The link requires no Lean
runtime or standard libraries and rejects writable state. Execution replays the
hash-bound native ECAM capture and tests every field, every non-dword position,
wrong inventory positions and invalid indices/selectors: 1,464 cases. The native
inventory hosted wrapper invokes this test. GCC and pinned Clang 18 are tested.

The functions are internal, without a new exported ABI. The production kernel
has not selected them. A complete snapshot loop must check exactly sixteen
entries and preserve the same private raw inputs across all calls; the
whole-loop proof and kernel integration remain pending. Successful inventory
comparison still establishes no Command policy, USB/TXE quiescence or DMA
containment and grants no permission to enter CPL3.
