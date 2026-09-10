# Unpublished closed-leaf construction

`construct.h` implements the physical-frame projection over the fixture's 4096
4-KiB leaves. It accepts at most 16 protected frames and 4096 exact required
leaves. Bounds and storage rejection happen before any input indexing or output
write that depends on those bounds. Required entries must be present, match the
source word exactly, and name an unprotected frame. Every rejection leaves the
output storage unchanged. Successful construction filters every physical alias,
independently of its U/S bit, and retains every other leaf word.

The caller supplies valid readable input arrays that remain immutable throughout
the call, and valid exclusive output storage of the fixed size. The constructor
rejects overlap between output and any input range; it does not establish pointer
validity. Inputs may overlap each other because all are read-only. Duplicate
protected frames are harmless; contradictory requirements reject.

This is a concrete experimental leaf operation corresponding to the projection
in `KernelUserRoot.closeChecked`, with additional bounded-storage and present-leaf
requirements. It is not a proved final-binary refinement. Inventories still need
to be complete for the selected scenario; exact expected words must come from
trusted construction, not simply be copied from an untrusted observation. The
52-bit physical-address mask is an encoding bound, not CPU physical-width
admission. Ancestors, huge-page exclusion, CPU controls, root addresses, ownership
lifetime, TLB invalidation and publication are separate obligations.

`construct-test.c` checks physical aliases (including the last virtual slot),
preservation of required mappings and an absent guard, and unchanged output on
required-map, overlap and bounds rejection. Empty inventories preserve the input;
that operation makes no user-isolation claim. The unpublished target may still
contain an old table after rejection and must never be published on failure.

The QEMU adapter freezes a snapshot of root A and validates identity mappings
for every page occupied by the linked fixture except the two protected data
pages. It tolerates only hardware A/D changes to the bootstrap leaf permissions.
It then builds root B using the constructor. Two no-SMAP cases reload root B and
require real not-present faults at the explicit alias and the identity alias.
A constructor mutation that omits filtering must instead reach the fixture's
failure exit. The 15-case reload suite includes these three cases and runs the
host construction test with the selected compiler. Evidence records the linked
constructor object's digest and uses separate compiler output directories.

The CI-wired `test-copy-root-construction.py` compares the concrete constructor
with the compiled `KernelUserRoot.closeChecked` model through a test-only canonical
leaf-word adapter. Its 33 cases include six required-mapping rejections and 27
accepted tables, comparing all 110,592 accepted leaf words. Rejected C outputs
must remain unchanged. The corpus excludes unmodeled A/D bits and invalid storage;
those are separate C tests. This is differential evidence, not a universal
refinement proof. The constructor is not used by the production kernel and does
not admit Qotom CPL3.

The transfer suite also requires constructed closed roots. Bootstrap populates
both copy aliases before freezing the source snapshot, and the constructor
removes them together with their identity aliases. Transfer setup subsequently
restricts the copy-root permissions and prepares exception stacks; it no longer
manually removes the second alias from the closed root. The transfer fixture
rejects builds that omit constructor integration. Each transfer evidence row
binds the linked constructor object digest, and its source manifest includes the
constructor and adapter. This composes construction with ordinary copies, partial
faults, failed cleanup and the existing single injected NMI checkpoint; production
entry and arbitrary interrupt timing remain outside this fixture's claim.
