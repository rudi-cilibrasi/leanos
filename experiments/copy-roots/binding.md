# Policy and subject-table binding

`UserCopyBinding.bind` first applies the entire `UserCopy.validate` policy, then
requires each location's subject-mode page-table classification to resolve to
its policy-authorized frame. Accepted lists preserve byte order and length.
The four proofs establish retained validation, exact walk/frame agreement,
length and policy-rejection precedence. This is a fresh-walk model, not a claim
about cached translations or a live hardware root.

`binding.h` implements the bounded two-page snapshot boundary. Its records
contain address-space ownership, page/object mappings and permissions, object
kind, live frame binding, allocator ownership, three ancestor words and a leaf
word. Shared object/frame records must agree. Duplicate virtual pages and
inconsistent records are rejected as malformed snapshots. The caller must
supply valid immutable storage and exclusively own unpublished output storage.
Rejections leave the entire output unchanged. Successful output can be passed
to the operand planner without reconstructing physical locations.

The snapshot is an input observation, not an authorization API for untrusted
callers. A production collector must derive policy records from trusted object
state, walk the actual subject root, verify ancestor links and supported page
sizes, and hold object lifetimes and mappings stable until transfer ends. This
adapter does none of that collection or locking. Two individually plausible
records do not prove that their source observations were simultaneous.

The concrete word domain allows P/RW/US, A/D, address bits and leaf NX; other
flags and large-page encodings are rejected. It uses a 52-bit address encoding
limit, not processor MAXPHYADDR admission. The Lean differential corpus uses
uniform ancestor words because the existing model has one shared ancestor path.
C storage/envelope checks and unsupported ancestor encodings are outside that
semantic comparison. The first production collector must respect these bounds.

The 205-case differential corpus covers every semantic result: success, all
policy rejection classes, and hardware mismatch. It includes zero-length
requests, overflow versus canonical-boundary precedence, cross-page aliases,
late policy rejection preceding earlier hardware failure, ancestor permissions,
changed leaf frames and A/D bits. The direct C tests additionally cover
malformed snapshots and poisoned-output preservation. The native Lean replay
also checks nine binding cases by kernel reduction.

All 22 transfer fixtures compose the binding adapter with the operand planner.
Their subject/object records are synthetic and use the fixture's linked data
frames; they are not captures of production subject roots or live ownership.
Existing fault/NMI/cleanup mutations remain downstream transfer tests. The
oversize helper-negative case intentionally passes seventeen against a validated
sixteen-byte plan. Full production root, entry/return, DMA/firmware and physical
Qotom admission remain open under issue #329 and its platform dependencies.
