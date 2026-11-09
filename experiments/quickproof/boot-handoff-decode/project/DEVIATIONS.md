# Deviations of the boot-handoff-decode project

The theorem is about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/handoff_unit.c`)

The functions of `include/boot_handoff_decode.h` are `static inline`. The
unit includes the header unchanged and gives five of them external names:

- `boot_handoff_extent` and `boot_handoff_project`, which `boot_allocate`
  calls in turn, as `handoff_extent` and `handoff_project`;
- `boot_handoff_decode_candidate`, which it calls for each candidate frame,
  as `handoff_candidate`;
- `boot_handoff_stream_copy` and `boot_handoff_decode_projection`, which
  `boot_handoff_project` composes and the lab capture calls alone, as
  `handoff_copy` and `handoff_projection`.

The wrappers only forward their arguments, and their bodies are proved like
every other function. The header has no `volatile` access, so the project
needs no `-Dvolatile=`: its decoder state is two arrays that the transitions
alternate between, and no state is copied.

## D2. A shim for the generated `boundary-abi.h` (`patch/boundary-abi.h`)

The generated header declares every Lean export. The shim declares only the
five the header calls, with the generated prototypes:

- `leanos_boot_handoff_stream_init` and `leanos_boot_handoff_stream_step`;
- `leanos_boot_decode_init_v5` and `leanos_boot_decode_step_v5`;
- `leanos_boot_projection_entry`.

## D3. The physical read is the law's

The kernel passes `boot_handoff_physical_read`, the eight-byte load at a
physical address through the boot identity map. With
`LEANOS_MALFORMED_HANDOFF_FIXTURE` it also sets bit 32 of the information's
first word, which leaves its `total_size` unchanged. The law passes its own
bootloader instead: a read that answers any eight bytes, a different value on
every call (so a re-read of the first word may disagree with the size read),
and that checks every call: the context and the address.

The proof does not depend on that bootloader. It holds for every callback
that returns a 64-bit value; the law instantiates it. The identity map, what
physical memory holds and whether it changes between reads stay a trusted
boundary, outside this theorem (issue #624).

## D4. The record of the projection's entries is the law's

The kernel passes `boot_projection_record_entry`, which stores the entry in
slot `slot` of its 256 `boot_projection_entries`. The law passes its own
record, which checks every call: the context, the slot (word 11 of the event
minus 1, below 256) and the entry (words 20 to 22), and that it comes after
the event's transition and before its block projections. The kernel's record
is safe only for a slot below 256, which the theorem states; the record's
store itself is outside it.

The header records entries through a callback, not by writing an array it is
given, because no code reads `boot_projection_entries`. GCC deletes the array
and its stores when the stores are direct, as they were before the refactor
and are in `boot_projection_record_entry`. Through a pointer it keeps the
6 KiB array, which moves the user pages and the first free frame, so the
serial transcripts would no longer be byte-identical to the code before the
refactor.

## D5. The Lean exports are the law's

The kernel links the header with the C that Lean compiles from
`LeanOS/BootMemoryMapStreaming.lean` and
`LeanOS/BootMemoryMapStreamAuthority.lean`. The law links it with its own
five functions of the same names and prototypes instead: an adversarial Lean
that may answer any value, a different one on every call. Each function
checks its call against the caller obligations of the exports'
documentation and the header's protocol:

- `initWord` (`leanos_boot_handoff_stream_init`): words 0 to 6 in order,
  with the stream identity the information's address;
- `stepWord` (`leanos_boot_handoff_stream_step`): words 0 to 8 of one
  transition in order, each with the same arguments ("replaying the same
  pure transition with a different query selector"), the state words 0 to 6
  of the previous answers committed together, a count of 8, the chunk's
  exact offset and bytes, and the terminal marker exactly at the last chunk;
- `initWordV5` (`leanos_boot_decode_init_v5`): words 0 to 40 in order, with
  target 0 for the projection and the candidate otherwise;
- `stepWordV5` (`leanos_boot_decode_step_v5`): words 0 to 40 of one
  transition in order, each with words 0 to 18 and 23 to 38 of the previous
  answers (words 19 to 22 are the one-step entry event and words 39 and 40
  the root selection, which the transition does not take), the stream
  identity, the chunk's offset and bytes, and the terminal marker;
- `projectionEntryWord` (`leanos_boot_projection_entry`): for each block of
  0 to 63 in order, words 1 to 4 in order, each with the event's entry, the
  block and the block's current usable and blocked words.

The header's proof does not depend on those functions. It holds for every
implementation that answers each call with a 64-bit value. What the answers
of the real exports mean is what the Lean definitions and theorems of
`LeanOS.BootMemoryMapStreaming` and `LeanOS.BootMemoryMapStreamAuthority`
state. The step that stays trusted is reading the law's protocol and the
exports' documentation as the same, and the calling convention: the
Lean-compiled functions take and return `uint64_t` as declared (ADR 0029).

## Not deviations, but limits of the law

- **Storage.** The kernel passes:
  - its 64-KiB `boot_handoff_copy`, 8-aligned, as 8192 words;
  - three bitmaps of 64 words;
  - two decoder states and the records, on `boot_allocate`'s stack or an
    adapter's.

  The law passes distinct objects of exactly these sizes, and for a decoding
  alone the words decoded as an object of exactly total / 8 words. The
  kernel decodes each candidate from the copy.
- **Extents.** A copy or a decoding alone takes an extent that is a multiple
  of 8 up to 65,536. That is what its callers pass: `boot_allocate` passes
  the extent `boot_handoff_extent` accepted, and the lab capture passes
  `boot_handoff_capture_length`'s, which applies the same bounds.
- **The kernel's composition.** `boot_allocate` observes the executing APIC
  ID between `boot_handoff_extent` and `boot_handoff_project`, an
  observation that may fail the handoff itself. The law calls the two in
  turn, with nothing between them.
- **Statuses.** The statuses the header returns are the theorem's. That the
  kernel's `boot_handoff_require` maps each to the reason of its check, and
  that `boot_allocate` calls the extent, the observation and the projection
  in that order before the ACPI copy, is outside it.
  `scripts/check-boot-handoff-stream.sh` checks both on the source.
- **The kernel's adapters.** `copy_boot_handoff`, `decode_boot_projection`
  and `decode_boot_candidate_authority` load the final state into the
  kernel's `struct boot_decode_state` through a volatile loop
  (`load_boot_decode_state`), so that Clang does not lower the copy to a
  `memcpy` call. That load, the kernel's use of the decoded words and the
  lab capture's composition of the steps are outside the theorem.
- **Concurrency.** The law is single-threaded: nothing else writes the copy,
  the bitmaps or the states while the header runs. That the copy stays
  immutable afterwards is the caller's obligation.
- **Termination.** The law states partial correctness: termination is not
  claimed, though every loop is bounded.
