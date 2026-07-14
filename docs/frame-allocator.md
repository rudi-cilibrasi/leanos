# Physical-frame allocator model

`LeanOS.FrameAllocator` is an executable, sequential reference model. A frame
identifier is a natural-numbered physical frame. The model stores the finite
list of modeled identifiers and a total status function whose sum type makes a
frame exactly one of reserved, free, or owned by one owner identifier.

Initialization expands normalized `{start, count, kind}` regions. Zero-sized
regions are rejected as malformed, and duplicate expanded identifiers are
rejected as overlaps. Reserved regions take their status from the input map;
all usable frames begin free. The firmware map's truthfulness remains a trusted
input assumption. Arithmetic overflow is absent from this natural-number model
and must be checked by any fixed-width boot adapter.

Allocation linearly scans the frame list for its first free entry, so it is
deterministic and takes O(n) time. Release and status lookup update or inspect a
functional map in O(1) in the model. Initialization expands and checks the
input with a simple list algorithm taking O(n²) time and O(n) space. These
choices favor small proofs over a production bitmap or free-list design.

## Machine-checked properties

- `conservation` classifies every modeled frame as reserved, free, or owned.
- `reserved_not_free` and `reserved_not_owned` prove class disjointness.
- `ownership_exclusive` proves one frame cannot have two different owners.
- `allocated_is_owned` and `allocated_not_reserved` characterize successful
  allocation and exclude reserved results.
- `released_is_free` and `invalid_release_explicit` prove valid release and
  explicit failure without silently adding a frame.

Executable examples cover fragmented input, malformed and overlapping maps,
exhaustion, invalid release, and reuse after a valid release.

## Capability coordination and boundaries

`OwnerId` is deliberately separate from `Capability.ObjectId`. A future kernel
operation must atomically create or validate the corresponding capability when
transferring a frame to an object, and must prevent capability use after frame
release or reuse. This model does not yet prove that cross-model refinement or
object-lifetime rule.

The model excludes page tables, virtual addresses, swapping, NUMA, concurrent
allocation, DMA, firmware validation, generated code, and boot integration.
Its theorems are model-level guarantees, not evidence that a kernel binary or
hardware allocator satisfies them.
