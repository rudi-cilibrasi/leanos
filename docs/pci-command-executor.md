# Ordered PCI Command writes and readbacks

`boot/pci-command-executor.h` executes the fifteen-step Qotom observation
contract through supplied callbacks. Before any access, it requires a complete
fifteen-function snapshot and acceptance from the supplied inventory checker.
The caller must use the complete Qotom inventory check, with success exactly
one. The executor does not maintain a second identity table.

It partitions the accepted canonical snapshot into downstream endpoints,
bus-zero endpoints, then bridges. Within each group it preserves snapshot
order. Each step writes a 16-bit zero to Command at offset four, then reads
all sixteen header dwords in ascending order. Readback Command must be zero.
Every other dword except Command/Status must equal the initial snapshot;
Status is allowed to change. A mismatch stops execution immediately, before
any subsequent read or write. There are at most fifteen writes and 240 reads,
with no retries, provided each callback terminates.

The output uses the existing 25-word trace slots. Count is reset before
validation and published only after the full sequence succeeds. A failure
retains the step, BDF, offset, successful write/read counts, and initial
admission result. Partial output cannot be used as a successful transition.
A failed write callback may already have affected hardware: successful-operation
counts do not imply that a failed operation had no effect. There is no rollback;
the caller must stop boot after any error.

The hosted test first runs complete-segment enumeration and feeds the collected
snapshot to this executor. Its admission callback invokes the actual generated
Qotom inventory export, and its completed trace enters the generated transition
export. Another success fixture permits volatile Status. Fault injection covers
every write, every read, every stable dword, every Command readback, initial
identity rejection, incorrect counts, and null arguments. Access counts and
addresses verify exact failure locations and absence of subsequent access.
The standalone enumeration script also compiles both routines freestanding
and checks for unresolved runtime symbols.

This is an executor and observation adapter, not an authorization to use its
callbacks on Qotom hardware. No hardware backend or production boot call is
installed. Callbacks must be trusted and serialized, the initial snapshot must
remain immutable, and output must not alias inputs. The inventory callback
is part of the trusted adapter. The caller must separately establish the board's
device/bridge policy, serial and recovery requirements, outstanding-transaction
handling, and absence/handling of concurrent agents. Clearing Command and
observing matching registers do not establish quiescence, IOMMU protection,
or device compliance. Issue #330 and whole-platform admission remain open.
