# Deviations of the boot-frame-selection project

The theorem is about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/frame_unit.c`)

The functions of `include/boot_frame_selection.h` are `static inline`. The
unit includes the header unchanged and gives its seven steps external names,
in the order `boot_allocate` calls them:

- `boot_frame_terminal` as `frame_terminal`;
- `boot_frame_select` as `frame_select`;
- `boot_frame_cross_check` as `frame_cross_check`;
- `boot_frame_scrub_selected` as `frame_scrub_selected`;
- `boot_frame_publication_result` and `boot_frame_publication_check` as
  `frame_publication_result` and `frame_publication_check`;
- `boot_frame_rescan`, which only the frame-budget scenario calls, as
  `frame_rescan`.

The wrappers only forward their arguments, and their bodies are proved like
every other function. The header has no `volatile` access, so the project
needs no `-Dvolatile=`: the scrub's physical stores and loads are the
kernel's callback, and the selected candidate's decoded state stays in the
state its decoder wrote, so no state is copied.

## D2. A shim for the generated `boundary-abi.h` (`patch/boundary-abi.h`)

The generated header declares every Lean export. The shim declares only the
six the header calls, with the generated prototypes:

- `leanos_boot_projection_manifest`, `leanos_boot_projection_free` and
  `leanos_boot_projection_finish`;
- `leanos_boot_manifest_candidate` and
  `leanos_boot_consume_exact_projection`;
- `leanos_boot_authority_result`.

## D3. The candidate decoder is the law's

The kernel passes `boot_frame_decode_candidate`. It runs
`boot_handoff_decode_candidate` of `include/boot_handoff_decode.h` over the
immutable handoff copy, with the candidate as its target frame, loads the
decoder's final state into the state it is given and returns the decoder's
status. The law passes its own decoder instead: for every call it writes any
41 words to the state it is given and answers any status, and it checks the
call: the context, the candidate and the state.

The proof does not depend on that decoder. It holds for every callback that
writes the 41 words of the state it is given and returns a 32-bit status;
the law instantiates it. That the kernel's decoder is project 8's, which
`experiments/quickproof/boot-handoff-decode` proves, is outside this
theorem: `scripts/check-boot-handoff-stream.sh` checks it on the source.

## D4. The scrub is the law's

The kernel passes `boot_frame_physical_scrub`: volatile stores of 0 to the
4,096 bytes of the frame through the boot identity map, then volatile loads
of each, reporting 0 at the first nonzero byte and 1 otherwise. The law
passes a scrub that answers any 32-bit value and checks the call: the context
and the frame. What physical memory does under the stores and loads, and the
identity map, stay a trusted boundary, outside this theorem (issue #627).

## D5. The Lean exports are the law's

The kernel links the header with the C that Lean compiles from
`LeanOS/BootMemoryMapStreamAuthority.lean`. The law links it with its own
six functions of the same names and prototypes instead: an adversarial Lean
that may answer any value, a different one on every call. Each function
checks its call against the caller obligations of the exports' documentation
and the header's protocol:

- `projectionManifestWord` (`leanos_boot_projection_manifest`): for each
  block of 0 to 63 in order, words 1 to 3 in order, each with the block and
  the 18 manifest words in their positional order;
- `projectionFreeWord` (`leanos_boot_projection_free`): once per block, with
  the block's usable and blocked words and the reservation mask its overlay
  answered ("reservation precedence ... for one bounded projection word");
- `projectionFinishWord` (`leanos_boot_projection_finish`): words 0 to 8 in
  order, each with the decoder's status, error, entry count and highest
  frame, the overlay's status and error (those of the last block that did
  not answer 1 and 0), owner 1, and the 64 free words in block order ("the
  complete canonical free projection");
- `manifestCandidate` (`leanos_boot_manifest_candidate`): once per decoded
  candidate, and once for the rescanned frame, with that frame and the
  manifest words;
- `consumeExactProjection` (`leanos_boot_consume_exact_projection`): once
  per decoded candidate, with no frame yet (4096), the candidate, the
  status, usable and blocked words of the state its decoder just wrote, and
  the manifest's answer for it;
- `authorityResultWord` (`leanos_boot_authority_result`): words 0 to 4 in
  order, each with the selected frame, the target frame, status, usable and
  blocked words of its decoded state, its manifest answer and a scrubbed
  frame, and, in `boot_allocate`'s sequence, only after the scrub reported
  the frame zeroed.

The header's proof does not depend on those functions. It holds for every
implementation that answers each call with a 64-bit value. What the answers
of the real exports mean is what the Lean definitions and theorems of
`LeanOS.BootMemoryMapStreamAuthority` state. The step that stays trusted is
reading the law's protocol and the exports' documentation as the same, and
the calling convention: the Lean-compiled functions take and return
`uint64_t` as declared (ADR 0029).

## Not deviations, but limits of the law

- **Storage.** The kernel passes:
  - its 18 manifest words (`BOOT_MANIFEST_ARGS`: link-time addresses and
    sizes, the information's address and extent) and the projection
    decoder's final state, on `boot_allocate`'s stack;
  - the projection's three 64-word bitmaps, kernel globals;
  - the terminal result, two decoder states, the publication result, the
    rescan's record and the selection's records, on `boot_allocate`'s
    stack.

  The law passes distinct objects of exactly these sizes.
- **The kernel's composition.** `boot_allocate` calls the steps in the order
  of the law's sequence, after the MADT admission and before its serial
  records, with the selection's records as the later steps' frames. Between
  the steps it keeps its production mutation fixtures:
  `LEANOS_PROJECTION_SELECTION_MUTATION_FIXTURE`,
  `LEANOS_RAW_SELECTION_MUTATION_FIXTURE` and
  `LEANOS_RAW_CLASSIFICATION_MUTATION_FIXTURE` between the selection and the
  cross-check, `LEANOS_PUBLICATION_RESULT_MUTATION_FIXTURE` between the
  authority result and its check. The law calls the steps with nothing
  between them; it calls each step alone with any arguments too, which
  covers the values a fixture gives the next step. In the frame-budget
  scenario, the kernel stores the published and the next frame in its
  globals before the rescan and the rescan's record in its globals after.
  The order, the fixtures' places and the globals are outside the theorem;
  `scripts/check-boot-handoff-stream.sh` checks the order and the fixtures'
  places on the source.
- **Statuses.** The statuses the header returns are the theorem's. That the
  kernel's `boot_frame_require` maps each to the reason of its check (and a
  decoder's rejection to the reason of the decoder's own status, through
  `boot_handoff_require`) is outside it; `scripts/check-boot-handoff-stream.sh`
  checks it on the source.
- **`take_next`.** The kernel passes 1 in the frame-budget scenario and 0
  otherwise. The law takes any value.
- **Concurrency.** The law is single-threaded: nothing else writes the
  bitmaps, the states or the results while the header runs.
- **Termination.** The law states partial correctness: termination is not
  claimed, though every loop is bounded.
