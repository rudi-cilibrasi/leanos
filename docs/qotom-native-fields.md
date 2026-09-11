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
has not selected them. The C loop in `boot/qotom-native-inventory.h` requires a completed scan,
exactly sixteen entries and success at every canonical index. Its snapshot and
checker binding must remain private and immutable throughout execution.
`QotomNativePCISnapshot.complete_snapshot` proves that this exact loop contract
produces a native witness preserving all supplied raw headers. The proof model's
lists and records are not runtime transport. Kernel integration remains pending. Successful inventory
comparison still establishes no Command policy, USB/TXE quiescence or DMA
containment and grants no permission to enter CPL3.

The test harness binds the C loop to the actual generated scalar checker and
also exercises the existing complete-segment collector. Snapshot tests cover
count/status/null rejection, every function's BDF/identity/layout changes,
bridge routing changes, duplicate rows, a missing function and failure at the
last scanned function. Source bytes remain unchanged. These are hosted reads
from the retained capture, not another physical boot.

The sanitized native-inventory wrapper additionally runs 158 standalone C-loop
and collector cases under the pinned GCC ASan/UBSan configuration. Its output
matches the ordinary executable. A seventeenth-header mutation must produce a
stack-buffer-overflow report in the inventory loop. Instrumentation covers the
C adapter and collector; the linked generated scalar object remains the one
checked independently for runtime dependencies, not a sanitizer-instrumented
Lean object.
