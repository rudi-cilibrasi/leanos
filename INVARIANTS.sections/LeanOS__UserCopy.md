# Copying data between a program and the kernel

When a program hands the kernel an address and asks it to read or write some bytes there, a careless kernel could be tricked into touching memory the program has no right to. These theorems show that LeanOS checks every single byte of the requested range first, for size, valid addressing, ownership, and permission, before moving anything; a request that fails any check changes nothing at all, and a request that passes copies exactly the checked bytes and not one byte more. In particular, a program can never use these copies to reach into memory owned by a different program.

- `validate_too_long` — A copy request longer than the fixed size limit is always refused, with the over-length reason, before anything else is considered.
- `validate_zero` — A zero-length copy request touches no address at all and is therefore always acceptable, whatever starting address it names.
- `validate_bounds` — Whenever a nonempty request passes validation, its entire byte range provably fits inside the machine's address space and inside the region the hardware treats as well-formed addresses.
- `validateLoop_length` — Bookkeeping: the byte-by-byte check produces exactly one verified location per requested byte, never more or fewer.
- `validate_length` — Bookkeeping: the same one-location-per-byte accounting holds for the whole-request validator, not just its inner loop.
- `validateLoop_authorized` — Every location the validator accepts was reached by translating an address inside the requested range, through the calling program's own address space, with exactly the permission the request asked for; nothing sneaks in from elsewhere.
- `copyFrom_rejected_unchanged` — A refused copy from a program's memory leaves the entire system state exactly as it was.
- `copyTo_rejected_unchanged` — A refused copy into a program's memory likewise leaves the entire system state exactly as it was.
- `copyFrom_preserves_user` — Copying data out of a program's memory never alters a single byte of that program's memory; the direction of data flow is strictly one-way.
- `copyTo_preserves_kernel` — Copying data into a program's memory never alters a single byte of the kernel's own buffers.
- `setKernelRange_outside` — Bookkeeping: writing values into one named kernel buffer leaves every other buffer, and every position past the supplied values, untouched.
- `copyFrom_validated_exact` — An accepted copy from a program installs in the chosen kernel buffer exactly the bytes read from the pre-checked locations, no substitutions and no extras.
- `copyFrom_outside` — An accepted copy from a program cannot change any kernel buffer other than the one named, nor any position beyond the requested length.
- `setUserLocations_outside` — Bookkeeping: writing bytes at a fixed list of pre-checked destinations leaves every physical byte outside that list untouched.
- `copyTo_validated_exact` — An accepted copy into a program writes exactly the chosen kernel-buffer values at exactly the complete pre-checked destination list.
- `copyTo_outside` — An accepted copy into a program leaves every physical byte outside its pre-checked destination list unchanged.
- `byteLocation_other_subject_rejected` — A program asking about an address space owned by a different program cannot even resolve the first byte; the lookup fails immediately with a not-the-owner refusal.
- `validateLoop_other_subject_rejected` — A stepping-stone fact: the byte-by-byte validator inherits that refusal, rejecting any nonempty range aimed at another program's address space.
- `copyFrom_other_subject_rejected` — Any in-bounds, nonempty attempt to copy data out of another program's memory is refused outright, with the not-the-owner reason.
- `copyTo_other_subject_rejected` — Any in-bounds, nonempty attempt to copy data into another program's memory is refused outright, with the not-the-owner reason.
