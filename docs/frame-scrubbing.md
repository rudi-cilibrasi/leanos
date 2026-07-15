# Atomic frame scrubbing

`LeanOS.FrameScrub` models the confidentiality step missing from capability
revocation: a physical frame is cleared before a new memory-object lifetime is
published. It reuses `MemoryLifecycle` as the only source of object bindings,
allocator ownership, and capability authority, and reuses `UserCopy`'s finite
frame-byte representation. One modeled frame is one 4 KiB page.

The policy is atomic allocation-time scrubbing. `MemoryLifecycle.allocate`
selects and owns a free frame; `FrameScrub.allocate` clears every modeled byte
and returns the new root capability and cleared contents together. No state in
which the new owner can observe a partially cleared frame is returned. Release
atomically retires the old binding and capabilities but leaves contents
arbitrary until the next allocation. There is no second ownership or
quarantine state.

## Proved and tested behavior

Lean proves that every accepted allocation publishes a current
allocator-owned frame whose first through last modeled bytes all equal zero,
independently of the prior byte function. Clearing one frame leaves every
other frame unchanged. Allocation and release rejection preserve the complete
state, release itself does not alter bytes, and the scrub/content invariant
connects an unwritten object lifetime to its lifecycle binding and allocator
owner. Given that invariant, an authorized read from an unwritten fresh
lifetime returns zero.

Executable traces start with arbitrary all-nonzero firmware contents, have
subject A write a nonzero sentinel at the first byte, release its object, and
reuse the same frame for subject B under a never-before-issued object ID.
Subject B reads zero at the first and last byte while A's stale capability is
rejected. Further examples cover exhaustion, repeated release, and a second
release/reuse cycle. These traces are tests of the executable model, not
additional proofs.

`writeByte` is the modeled owner-write transition: after its authorization
check it changes one byte and records that the current object lifetime has
written. Reads and writes outside the 4 KiB frame reject. The existing
`UserCopy` model remains the mapping/range authorization boundary; this slice
does not introduce a second virtual-address policy. Subject termination may
reuse this same release/publication policy, but does not establish a separate
zeroization path.

## Trust boundary and non-goals

The theorem concerns the Lean state transition only. It does not prove that a
compiler-generated `memset`, assembly loop, cache writeback, QEMU, firmware,
or physical DRAM implements the transition. QEMU success and compilation are
integration evidence, not physical-erasure evidence. Firmware contents and
old-owner writes may be arbitrary; the proof relies on the modeled scrub, not
an initial-zero assumption.

Cryptographic erasure, DMA and devices, swap, persistence, crash dumps,
reserved firmware memory, caches and speculation, power loss, concurrency,
background clearing, huge pages, shared memory, and performance or
constant-time claims are outside this model. It adds no axiom, proof escape,
unsafe or extern declaration, FFI, or trusted implementation.
