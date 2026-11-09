#ifndef LEANOS_BOOT_FRAME_SELECTION_H
#define LEANOS_BOOT_FRAME_SELECTION_H
#include <stdint.h>
#include "boundary-abi.h"

/* The frame selection, scrub and publication of boot_allocate (#627): the C
 * that turns the generated decoder's answers into the one frame the boot
 * allocator publishes.  It runs after the MADT admission, on the bounded
 * projection and the decoder's final state that include/boot_handoff_decode.h
 * produced, and calls six exports of LeanOS/BootMemoryMapStreamAuthority.lean.
 * Its steps, which boot_allocate calls in this order:
 *
 * - boot_frame_terminal overlays the reservation manifest on the projection
 *   and asks the projection's terminal result;
 * - boot_frame_select replays the handoff for each candidate frame through
 *   the candidate decoder and selects the first that the exact-projection
 *   consumer accepts (and, for the frame-budget scenario, the next one);
 * - boot_frame_cross_check requires the projection's nomination, the
 *   selected candidate's decoded state and the manifest to agree with the
 *   selection;
 * - boot_frame_scrub_selected zeroes the selected frame and reads it back;
 * - boot_frame_publication_result asks the authority result, and
 *   boot_frame_publication_check requires it to publish the selected frame;
 * - boot_frame_rescan, in the frame-budget scenario only, decodes the next
 *   frame again and requires its authority.
 *
 * The steps are separate functions so that the kernel's production mutation
 * fixtures keep their place between them (boot/kernel.c: boot_allocate).
 * The candidate decoder and the scrub are callbacks: the kernel's decoder is
 * include/boot_handoff_decode.h's boot_handoff_decode_candidate over the
 * handoff copy, and its scrub the volatile stores and loads through the boot
 * identity map, so no physical access is here.  The manifest, the bitmaps,
 * the decoder states and every result are arguments.  Every check returns a
 * status, and the caller maps each status to the failure reason of its check
 * (boot/kernel.c: boot_frame_require).  No function here returns or copies a
 * struct by value, writes through a volatile pointer or uses a global, so
 * QuickProof's clightgen and VST take this header
 * (experiments/quickproof/boot-frame-selection). */

/* The boot-accessible frames (the projection's 64 bitmap blocks of 64
   frames), the decoder's state words, and the words of the reservation
   manifest, the terminal result, the publication result and the rescan's
   record. */
#define BOOT_FRAME_COUNT UINT64_C(4096)
#define BOOT_FRAME_BLOCKS 64
#define BOOT_FRAME_DECODE_WORDS 41
#define BOOT_FRAME_MANIFEST_WORDS 18
#define BOOT_FRAME_TERMINAL_WORDS 9
#define BOOT_FRAME_PUBLICATION_WORDS 5
#define BOOT_FRAME_RESCAN_WORDS 5

/* The statuses, in the order of the checks.  The comment before each group
   names the failure reason boot_allocate gives for all of it. */
enum boot_frame_status {
    BOOT_FRAME_OK,
    /* projection-terminal: the terminal result answered word 0 (version)
       other than 1, word 1 (status) other than 1, word 2 (error) other than
       0, word 3 (the nominated frame) not below 4096, word 4 (owner) other
       than 1, or word 5 (entry count) other than the decoder's. */
    BOOT_FRAME_TERMINAL_VERSION,
    BOOT_FRAME_TERMINAL_STATUS,
    BOOT_FRAME_TERMINAL_ERROR,
    BOOT_FRAME_TERMINAL_FRAME,
    BOOT_FRAME_TERMINAL_OWNER,
    BOOT_FRAME_TERMINAL_ENTRY_COUNT,
    /* The candidate decoder rejected a candidate: its own nonzero status is
       written to the caller's record, and the kernel gives that status's
       reason (authority-init or authority-rejected). */
    BOOT_FRAME_DECODER,
    /* projection-authority (raw-selection-authority under the raw-selection
       mutation fixture): no frame is selected (the frame is not below 4096);
       the projection's nomination (terminal word 3) or the selected state's
       target frame (word 16) is not the selected frame; that state's entry
       count (word 11) or highest frame (word 17) is not the decoder's; it is
       not usable (word 14 is not 1) or is blocked (word 15 is not 0); or the
       manifest's answer for the frame is not 1. */
    BOOT_FRAME_AUTHORITY_NONE,
    BOOT_FRAME_AUTHORITY_NOMINATION,
    BOOT_FRAME_AUTHORITY_TARGET,
    BOOT_FRAME_AUTHORITY_ENTRY_COUNT,
    BOOT_FRAME_AUTHORITY_HIGHEST,
    BOOT_FRAME_AUTHORITY_USABLE,
    BOOT_FRAME_AUTHORITY_BLOCKED,
    BOOT_FRAME_AUTHORITY_MANIFEST,
    /* scrub: the scrub did not report a zeroed frame. */
    BOOT_FRAME_SCRUB,
    /* publication: the authority result answered word 0 (version) other
       than 1, word 1 (status) other than 1, word 2 (error) other than 0,
       word 3 other than the selected frame or word 4 (the published object)
       other than the selected frame plus 1. */
    BOOT_FRAME_PUBLICATION_VERSION,
    BOOT_FRAME_PUBLICATION_STATUS,
    BOOT_FRAME_PUBLICATION_ERROR,
    BOOT_FRAME_PUBLICATION_FRAME,
    BOOT_FRAME_PUBLICATION_OBJECT,
    /* frame-budget-unpublished-frame: the next frame is not below 4096, or
       not above the published frame. */
    BOOT_FRAME_UNPUBLISHED_LIMIT,
    BOOT_FRAME_UNPUBLISHED_ORDER,
    /* frame-budget-projection-authority: the next frame's state has an entry
       count (word 11) or a highest frame (word 17) other than the decoder's,
       a target frame (word 16) other than the next frame, a status (word 1)
       other than 1, a usable word (14) other than 1 or a blocked word (15)
       other than 0, or the manifest does not admit the frame. */
    BOOT_FRAME_RESCAN_ENTRY_COUNT,
    BOOT_FRAME_RESCAN_HIGHEST,
    BOOT_FRAME_RESCAN_TARGET,
    BOOT_FRAME_RESCAN_STATUS,
    BOOT_FRAME_RESCAN_USABLE,
    BOOT_FRAME_RESCAN_BLOCKED,
    BOOT_FRAME_RESCAN_MANIFEST
};

/* Decode the handoff again with `candidate` as the target frame: write the
   decoder's final state, its BOOT_FRAME_DECODE_WORDS words, to `state`, and
   return 0 when the decoder accepted the handoff for the candidate, or its
   nonzero status otherwise.  The kernel's decoder is
   boot_handoff_decode_candidate over the immutable handoff copy, and returns
   its statuses (include/boot_handoff_decode.h). */
typedef uint32_t (*boot_frame_decode)(void *context, uint64_t candidate,
                                      uint64_t *state);

/* Zero the 4096 bytes of physical frame `frame`, then read them back: return
   1 when every byte read back 0, and anything else otherwise.  The kernel's
   scrub (volatile stores and loads through the boot identity map) is a
   trusted boundary. */
typedef uint32_t (*boot_frame_scrub)(void *context, uint64_t frame);

/* The 18 words of the reservation manifest, in the positional order of the
   exports: low memory, the loaded image, the page tables, the descriptor
   tables, the kernel stacks, the ordinary-entry guard, the ordinary-entry
   stack, the embedded users and the Multiboot information, each a start and
   a length. */
#define BOOT_FRAME_MANIFEST_ARGS(m) \
    (m)[0], (m)[1], (m)[2], (m)[3], (m)[4], (m)[5], (m)[6], (m)[7], \
    (m)[8], (m)[9], (m)[10], (m)[11], (m)[12], (m)[13], (m)[14], (m)[15], \
    (m)[16], (m)[17]

#define BOOT_FRAME_BITMAP_ARGS(w) \
    (w)[0], (w)[1], (w)[2], (w)[3], (w)[4], (w)[5], (w)[6], (w)[7], \
    (w)[8], (w)[9], (w)[10], (w)[11], (w)[12], (w)[13], (w)[14], (w)[15], \
    (w)[16], (w)[17], (w)[18], (w)[19], (w)[20], (w)[21], (w)[22], (w)[23], \
    (w)[24], (w)[25], (w)[26], (w)[27], (w)[28], (w)[29], (w)[30], (w)[31], \
    (w)[32], (w)[33], (w)[34], (w)[35], (w)[36], (w)[37], (w)[38], (w)[39], \
    (w)[40], (w)[41], (w)[42], (w)[43], (w)[44], (w)[45], (w)[46], (w)[47], \
    (w)[48], (w)[49], (w)[50], (w)[51], (w)[52], (w)[53], (w)[54], (w)[55], \
    (w)[56], (w)[57], (w)[58], (w)[59], (w)[60], (w)[61], (w)[62], (w)[63]

/* The manifest overlay and the projection's terminal result.  For each block
   b of 0 to 63 in order it asks leanos_boot_projection_manifest words 1, 2
   and 3 (status, error and reservation mask) of block b with the manifest,
   writes word 3 to reserved[b], and asks leanos_boot_projection_free for the
   block's free word from usable[b], blocked[b] and that mask.  The
   manifest's status and error are 1 and 0, unless a block answered another
   status or error: then those of the last such block.  Then it asks
   leanos_boot_projection_finish words 0 to 8, into terminal, with the
   decoder's status, error, entry count and highest frame (words 1, 2, 11 and
   17 of `decoded`, the projection decoder's final state), the manifest's
   status and error, owner 1 and the 64 free words; and it accepts the result
   only when words 0 to 5 are 1, 1, 0, a frame below 4096, 1 and the
   decoder's entry count.  The terminal words are written whatever the checks
   decide. */
static inline enum boot_frame_status boot_frame_terminal(
        const uint64_t *manifest, const uint64_t *decoded,
        const uint64_t *usable, const uint64_t *blocked, uint64_t *reserved,
        uint64_t *terminal) {
    uint64_t free_words[BOOT_FRAME_BLOCKS];
    uint64_t manifest_status = 1, manifest_error = 0;
    for (uint64_t block = 0; block < BOOT_FRAME_BLOCKS; ++block) {
        const uint64_t status = leanos_boot_projection_manifest(
            block, BOOT_FRAME_MANIFEST_ARGS(manifest), 1);
        const uint64_t error = leanos_boot_projection_manifest(
            block, BOOT_FRAME_MANIFEST_ARGS(manifest), 2);
        const uint64_t mask = leanos_boot_projection_manifest(
            block, BOOT_FRAME_MANIFEST_ARGS(manifest), 3);
        if (status != 1 || error != 0) {
            manifest_status = status;
            manifest_error = error;
        }
        reserved[block] = mask;
        free_words[block] = leanos_boot_projection_free(
            usable[block], blocked[block], mask);
    }
    for (uint64_t query = 0; query < BOOT_FRAME_TERMINAL_WORDS; ++query)
        terminal[query] = leanos_boot_projection_finish(
            decoded[1], decoded[2], manifest_status, manifest_error,
            decoded[11], decoded[17], 1, query,
            BOOT_FRAME_BITMAP_ARGS(free_words));
    if (terminal[0] != 1) return BOOT_FRAME_TERMINAL_VERSION;
    if (terminal[1] != 1) return BOOT_FRAME_TERMINAL_STATUS;
    if (terminal[2] != 0) return BOOT_FRAME_TERMINAL_ERROR;
    if (terminal[3] >= BOOT_FRAME_COUNT) return BOOT_FRAME_TERMINAL_FRAME;
    if (terminal[4] != 1) return BOOT_FRAME_TERMINAL_OWNER;
    if (terminal[5] != decoded[11]) return BOOT_FRAME_TERMINAL_ENTRY_COUNT;
    return BOOT_FRAME_OK;
}

/* Select from target-specific replays of the immutable raw handoff.  For each
   candidate frame 0, 1, ... below 4096 in order it decodes the handoff for the
   candidate through `decode` into states[0], asks
   leanos_boot_manifest_candidate for the candidate with the manifest, then
   leanos_boot_consume_exact_projection with no frame yet (4096), the
   candidate, the decoded status, usable and blocked words (words 1, 14 and
   15) and the manifest's answer.  The first answer below 4096 is the
   selected frame, with that candidate's manifest answer, and states[0] keeps
   its decoded state.  With `take_next` nonzero (the frame-budget scenario)
   the scan goes on, decoding into states[1], and the next answer below 4096
   is the next frame.  The scan stops there, or after the last candidate; a
   frame not found is 4096, with manifest answer 0.  On BOOT_FRAME_OK the
   selected frame, its manifest answer and the next frame are written to
   `selected`, `selected_manifest` and `next`.  When the decoder rejects a
   candidate it returns BOOT_FRAME_DECODER at once and writes the decoder's
   status to `decoder_status`.  Nothing else is written but the states. */
static inline enum boot_frame_status boot_frame_select(
        boot_frame_decode decode, void *context, const uint64_t *manifest,
        uint32_t take_next, uint64_t states[2][BOOT_FRAME_DECODE_WORDS],
        uint64_t *selected, uint64_t *selected_manifest, uint64_t *next,
        uint32_t *decoder_status) {
    uint64_t first = BOOT_FRAME_COUNT, first_manifest = 0;
    uint64_t second = BOOT_FRAME_COUNT;
    uint32_t scan = 0;
    for (uint64_t candidate = 0; candidate < BOOT_FRAME_COUNT; ++candidate) {
        uint64_t *state = states[scan];
        const uint32_t status = decode(context, candidate, state);
        if (status != 0) {
            *decoder_status = status;
            return BOOT_FRAME_DECODER;
        }
        const uint64_t candidate_manifest = leanos_boot_manifest_candidate(
            candidate, BOOT_FRAME_MANIFEST_ARGS(manifest));
        const uint64_t exact_candidate = leanos_boot_consume_exact_projection(
            BOOT_FRAME_COUNT, candidate, state[1], state[14], state[15],
            candidate_manifest);
        if (exact_candidate >= BOOT_FRAME_COUNT) continue;
        if (scan == 0) {
            first = exact_candidate;
            first_manifest = candidate_manifest;
            if (take_next == 0) break;
            scan = 1;
        } else {
            second = exact_candidate;
            break;
        }
    }
    *selected = first;
    *selected_manifest = first_manifest;
    *next = second;
    return BOOT_FRAME_OK;
}

/* The authority cross-check of the selection: `selected` must be a frame
   below 4096 that is both the projection's nomination (terminal word 3) and
   the target frame (word 16) of `state`, the selected candidate's decoded
   state; that state's entry count and highest frame (words 11 and 17) must
   be the projection decoder's (`decoded`), it must be usable (word 14 is 1)
   and not blocked (word 15 is 0), and the manifest's answer for the frame
   must be 1.  It writes nothing. */
static inline enum boot_frame_status boot_frame_cross_check(
        const uint64_t *terminal, const uint64_t *decoded, uint64_t selected,
        const uint64_t *state, uint64_t selected_manifest) {
    if (selected >= BOOT_FRAME_COUNT) return BOOT_FRAME_AUTHORITY_NONE;
    if (terminal[3] != selected) return BOOT_FRAME_AUTHORITY_NOMINATION;
    if (state[16] != selected) return BOOT_FRAME_AUTHORITY_TARGET;
    if (state[11] != decoded[11]) return BOOT_FRAME_AUTHORITY_ENTRY_COUNT;
    if (state[17] != decoded[17]) return BOOT_FRAME_AUTHORITY_HIGHEST;
    if (state[14] != 1) return BOOT_FRAME_AUTHORITY_USABLE;
    if (state[15] != 0) return BOOT_FRAME_AUTHORITY_BLOCKED;
    if (selected_manifest != 1) return BOOT_FRAME_AUTHORITY_MANIFEST;
    return BOOT_FRAME_OK;
}

/* Scrub the selected frame once through `scrub`, which must report 1. */
static inline enum boot_frame_status boot_frame_scrub_selected(
        boot_frame_scrub scrub, void *context, uint64_t selected) {
    if (scrub(context, selected) != 1) return BOOT_FRAME_SCRUB;
    return BOOT_FRAME_OK;
}

/* The publication's authority result: words 0 to 4 of
   leanos_boot_authority_result, into `publication`, for the selected frame,
   the target frame, status, usable and blocked words of its decoded state
   (words 16, 1, 14 and 15 of `state`), its manifest answer and a scrubbed
   frame (1).  The caller asks it only once the scrub succeeded. */
static inline void boot_frame_publication_result(
        uint64_t selected, const uint64_t *state, uint64_t selected_manifest,
        uint64_t *publication) {
    for (uint64_t query = 0; query < BOOT_FRAME_PUBLICATION_WORDS; ++query)
        publication[query] = leanos_boot_authority_result(
            selected, state[16], state[1], state[14], state[15],
            selected_manifest, 1, query);
}

/* The publication check: the authority result must answer words 0 to 4 as
   1, 1, 0, the selected frame and the selected frame plus 1 (the published
   object).  It writes nothing. */
static inline enum boot_frame_status boot_frame_publication_check(
        uint64_t selected, const uint64_t *publication) {
    if (publication[0] != 1) return BOOT_FRAME_PUBLICATION_VERSION;
    if (publication[1] != 1) return BOOT_FRAME_PUBLICATION_STATUS;
    if (publication[2] != 0) return BOOT_FRAME_PUBLICATION_ERROR;
    if (publication[3] != selected) return BOOT_FRAME_PUBLICATION_FRAME;
    if (publication[4] != selected + 1) return BOOT_FRAME_PUBLICATION_OBJECT;
    return BOOT_FRAME_OK;
}

/* The frame-budget rescan of `next`, the next frame of boot_frame_select,
   after `published`, the published one: `next` must be below 4096 and above
   `published`.  Then it decodes the handoff for `next` through `decode` into
   `state` (a decoder's rejection returns BOOT_FRAME_DECODER and writes its
   status to `decoder_status`), asks leanos_boot_manifest_candidate for
   `next` with the manifest, and requires the state's entry count and
   highest frame (words 11 and 17) to be the projection decoder's
   (`decoded`), its target frame (word 16) to be `next`, its status (word 1)
   to be 1, its usable and blocked words (14 and 15) to be 1 and 0, and the
   manifest's answer to be 1.  On BOOT_FRAME_OK the target frame, status,
   usable and blocked words and the manifest's answer are written to
   rescan[0] to rescan[4]. */
static inline enum boot_frame_status boot_frame_rescan(
        boot_frame_decode decode, void *context, const uint64_t *manifest,
        const uint64_t *decoded, uint64_t published, uint64_t next,
        uint64_t *state, uint64_t *rescan, uint32_t *decoder_status) {
    if (next >= BOOT_FRAME_COUNT) return BOOT_FRAME_UNPUBLISHED_LIMIT;
    if (next <= published) return BOOT_FRAME_UNPUBLISHED_ORDER;
    const uint32_t status = decode(context, next, state);
    if (status != 0) {
        *decoder_status = status;
        return BOOT_FRAME_DECODER;
    }
    const uint64_t next_manifest = leanos_boot_manifest_candidate(
        next, BOOT_FRAME_MANIFEST_ARGS(manifest));
    if (state[11] != decoded[11]) return BOOT_FRAME_RESCAN_ENTRY_COUNT;
    if (state[17] != decoded[17]) return BOOT_FRAME_RESCAN_HIGHEST;
    if (state[16] != next) return BOOT_FRAME_RESCAN_TARGET;
    if (state[1] != 1) return BOOT_FRAME_RESCAN_STATUS;
    if (state[14] != 1) return BOOT_FRAME_RESCAN_USABLE;
    if (state[15] != 0) return BOOT_FRAME_RESCAN_BLOCKED;
    if (next_manifest != 1) return BOOT_FRAME_RESCAN_MANIFEST;
    rescan[0] = state[16];
    rescan[1] = state[1];
    rescan[2] = state[14];
    rescan[3] = state[15];
    rescan[4] = next_manifest;
    return BOOT_FRAME_OK;
}

#endif
