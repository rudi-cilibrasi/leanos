# Bounded copy-operand projection

`operands.h` implements the accepted-location projection modeled by
`UserCopyAliases.project` and `UserCopyOperands.operands`. It consumes at most
16 previously validated physical byte locations, deduplicates frames in first
appearance order, and emits two supervisor NX alias leaves plus ordered source
and destination byte addresses. Copy-in aliases are read-only; copy-out aliases
are writable. Unused leaves and operand slots are zero.

The caller must establish whole-request pointer validation, direction permission,
subject ownership, current lifetime, and stable mappings before calling it.
Supplying arbitrary locations does not establish any of those properties. The
kernel buffer must be a trusted bounded object, disjoint from protected physical
frames and indispensable planner storage. The caller owns unpublished output
storage exclusively and keeps all inputs immutable. This planner does not walk
page tables, install roots, invalidate translations, or publish lifetime claims.

The initial C domain uses two adjacent pages in the fixture's 16-MiB virtual
arena. Both closed-root slots must contain zero. Bounds, unprotected frames,
more than two distinct frames, occupied slots, invalid direction, and overlapping
output/input storage are rejected before any output write. A kernel buffer
intersecting either virtual alias slot is rejected too. These local checks do
not establish physical disjointness or completeness of the protected inventory.

The test-only Lean bridge compares 136 accepted cases covering every length
from zero through sixteen, both directions, repeated frames, reversed physical
frame order, page-boundary offsets and randomized offsets. It compares complete
alias words and every active byte operand with the existing model definitions.
It does not exercise `UserCopy.validate` or prove C refinement. Direct C tests
separately cover rejection and unchanged output; GCC sanitizer checks can run
on the same host test.

Every transfer fixture now obtains its aliases and operands from this planner.
The fixture supplies authority from its two linked data pages, rather than from
production subject validation. The oversize helper-negative case deliberately
passes count seventeen against a sixteen-byte plan to test the assembly bound.
Fault injection removes a planned alias after preparation. After successful
copy-out closure, fixture-only inspection restores both aliases so it can inspect
sentinels even for zero-length requests. These mutations and inspection mappings
are not part of the admitted transfer. Each evidence row binds the planner
object digest, and the manifest binds its sources.

This is execution-fixture composition for issue #329. Production pointer
validation, mapping publication and lifetime control, complete entry/return
integration and physical Qotom CPL3 evidence remain required.
