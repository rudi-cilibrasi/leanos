/* The state of the law frame_selection_exact (harness/frame_selection_exact.c): the reference model the law's
   candidate decoder, scrub and Lean exports keep while the header runs.  env/frame_selection_exact.c reads it too,
   to shape native and interpreter runs; it is part of no theorem through the env. */
#ifndef LEANOS_FRAME_SELECTION_EXACT_H
#define LEANOS_FRAME_SELECTION_EXACT_H
#include <stdint.h>
#include "frame_api.h"

/* The function main calls. */
#define CALL_ALLOCATE 0u      /* boot_allocate's sequence: every step below in turn, while each returns OK */
#define CALL_TERMINAL 1u      /* boot_frame_terminal */
#define CALL_SELECT 2u        /* boot_frame_select */
#define CALL_CROSS_CHECK 3u   /* boot_frame_cross_check */
#define CALL_SCRUB 4u         /* boot_frame_scrub_selected */
#define CALL_PUBLICATION 5u   /* boot_frame_publication_result, then boot_frame_publication_check */
#define CALL_RESCAN 6u        /* boot_frame_rescan */
#define CALLS 7u

/* The step being run. */
#define STEP_TERMINAL 0u
#define STEP_SELECT 1u
#define STEP_CROSS_CHECK 2u
#define STEP_SCRUB 3u
#define STEP_PUBLICATION_RESULT 4u
#define STEP_PUBLICATION_CHECK 5u
#define STEP_RESCAN 6u

/* The call the header may make next. */
#define EXPECT_MANIFEST 0u     /* the manifest overlay of block `block`: word `word` of 1..3 */
#define EXPECT_FREE 1u         /* the free word of block `block` */
#define EXPECT_FINISH 2u       /* the terminal result: word `word` of 0..8 */
#define EXPECT_DECODE 3u       /* the candidate decoder: candidate `candidate` into state `scan` */
#define EXPECT_CANDIDATE 4u    /* the manifest's answer for candidate `candidate` */
#define EXPECT_CONSUME 5u      /* the exact-projection consumer for candidate `candidate` */
#define EXPECT_SCRUB 6u        /* the scrub of frame `selected` */
#define EXPECT_AUTHORITY 7u    /* the authority result: word `word` of 0..4 */
#define EXPECT_NOTHING 8u      /* no call: the function must return `verdict` */

#define FRAMES BOOT_FRAME_COUNT
#define BLOCKS BOOT_FRAME_BLOCKS
#define WORDS BOOT_FRAME_DECODE_WORDS
#define MANIFEST BOOT_FRAME_MANIFEST_WORDS
#define TERMINAL BOOT_FRAME_TERMINAL_WORDS
#define PUBLICATION BOOT_FRAME_PUBLICATION_WORDS
#define RESCAN BOOT_FRAME_RESCAN_WORDS

/* main draws its inputs in this order, each any 64-bit value (two nondet_u32, the high half first): the function
   and take_next (their low 32 bits), the four frame arguments of the steps alone, then the prior values of every
   object word, then of the four records. */
#define DRAW_CALL 0
#define DRAW_TAKE_NEXT 1
#define DRAW_SELECTED 2
#define DRAW_SELECTED_MANIFEST 3
#define DRAW_PUBLISHED 4
#define DRAW_NEXT 5
#define DRAW_MANIFEST 6
#define DRAW_DECODED (DRAW_MANIFEST + MANIFEST)
#define DRAW_USABLE (DRAW_DECODED + WORDS)
#define DRAW_BLOCKED (DRAW_USABLE + BLOCKS)
#define DRAW_RESERVED (DRAW_BLOCKED + BLOCKS)
#define DRAW_TERMINAL (DRAW_RESERVED + BLOCKS)
#define DRAW_STATES (DRAW_TERMINAL + TERMINAL)
#define DRAW_PUBLICATION (DRAW_STATES + 2 * WORDS)
#define DRAW_RESCAN (DRAW_PUBLICATION + PUBLICATION)
#define DRAW_RECORDS (DRAW_RESCAN + RESCAN)   /* selected, its manifest answer, next, the decoder's status */
#define DRAWS (DRAW_RECORDS + 4)

struct law {
    /* The function, take_next, and the frame arguments of the steps alone: the selected frame and its manifest
       answer (the cross-check, the scrub and the publication), the published and the next frame (the rescan). */
    uint32_t call, take_next;
    uint64_t selected, selected_manifest, published, next;
    /* Set by main just before it calls the header: the env serves answers from then on. */
    uint32_t running;
    /* What memory must hold when each function returns: the inputs (unchanged), the projection's reserved bitmap,
       the terminal result, the two decoder states, the publication result and the rescan's record, each as before
       the call where the function was not asked to write; and the four records. */
    uint64_t manifest[MANIFEST], decoded[WORDS], usable[BLOCKS], blocked[BLOCKS];
    uint64_t reserved_expect[BLOCKS], terminal_expect[TERMINAL], states_expect[2][WORDS];
    uint64_t publication_expect[PUBLICATION], rescan_expect[RESCAN];
    uint64_t selected_expect, manifest_expect, next_expect;
    uint32_t decoder_expect;
    /* The header's states, for the decoder's check of the state it is given. */
    uint64_t (*states)[WORDS];
    /* The protocol. */
    uint32_t step, expect, verdict;
    uint64_t block, word, candidate;
    uint32_t scan;               /* the state the decoder writes: states[scan] */
    uint64_t manifest_status, manifest_error;   /* the overlay's, as the terminal result must be asked them */
    uint64_t free_words[BLOCKS];                /* the free words answered */
    uint64_t candidate_manifest;                /* the manifest's answer for the current candidate */
    uint64_t first, first_manifest, second;     /* the selection so far */
    uint64_t answer[4];                         /* the answers to the current block's overlay */
    uint32_t scrubbed;                          /* the scrub reported the frame zeroed */
};
extern struct law law;
#endif
