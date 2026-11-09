/* The state of the law handoff_decode_exact (harness/handoff_decode_exact.c): the reference model the law's
   bootloader and Lean exports keep while the header runs.  env/handoff_decode_exact.c reads it too, to shape
   native and interpreter runs; it is part of no theorem through the env. */
#ifndef LEANOS_HANDOFF_DECODE_EXACT_H
#define LEANOS_HANDOFF_DECODE_EXACT_H
#include <stdint.h>
#include "handoff_api.h"

/* The function main calls. */
#define CALL_ALLOCATE 0u     /* boot_handoff_extent, then boot_handoff_project when it returns OK */
#define CALL_COPY 1u         /* boot_handoff_stream_copy */
#define CALL_PROJECTION 2u   /* boot_handoff_decode_projection */
#define CALL_CANDIDATE 3u    /* boot_handoff_decode_candidate */

/* The call the header may make next. */
#define EXPECT_SIZE 0u         /* the bootloader: the information's first eight bytes */
#define EXPECT_STREAM_INIT 1u  /* the stream reset: word `word` of 0..6 */
#define EXPECT_CHUNK 2u        /* the bootloader: chunk `chunk` */
#define EXPECT_STREAM_STEP 3u  /* chunk `chunk`'s stream transition: word `word` of 0..8 */
#define EXPECT_DECODE_INIT 4u  /* the decoder reset: word `word` of 0..40 */
#define EXPECT_DECODE_STEP 5u  /* chunk `chunk`'s decoder transition: word `word` of 0..40 */
#define EXPECT_RECORD 6u       /* the record of the entry event of chunk `chunk` */
#define EXPECT_ENTRY 7u        /* the event's projection into block `block`: word `word` + 1 of 1..4 */
#define EXPECT_NOTHING 8u      /* no call: the function must return `verdict` */

#define WORDS BOOT_DECODE_WORDS
#define COPY_WORDS BOOT_HANDOFF_MAX_WORDS
#define ENTRIES BOOT_PROJECTION_ENTRIES
#define BLOCKS BOOT_PROJECTION_BLOCKS

struct law {
    /* The arguments: the function, the magic, the information's address, the extent (for an allocation, the
       one the size read declares), the target frame (0 with a projection) and whether the decoder builds a
       projection. */
    uint32_t call, magic, address, total;
    uint64_t candidate;
    uint32_t projection;
    /* Set by main just before it calls the header: the env serves answers from then on. */
    uint32_t running;
    /* What memory must hold when the function returns: the copy, the projection's bitmaps and the decoder's two
       states, each as before the call where the function was not asked to write; and the words the decoder reads
       (the copy for an allocation, the law's own object otherwise). */
    uint64_t *copy_expect, *info_expect;
    uint64_t usable_expect[BLOCKS], blocked_expect[BLOCKS], reserved_expect[BLOCKS];
    uint64_t states_expect[2][WORDS];
    uint32_t at;           /* the decoder's current state: states_expect[at] */
    uint32_t extent_ok;    /* the size read declared an extent the bounds accept */
    uint32_t records;      /* the entries recorded */
    /* The protocol. */
    uint32_t expect, verdict;
    uint64_t chunk, word, block;
    uint64_t value;        /* the current chunk: as the bootloader answered it (stream), or the copy's word (decoder) */
    uint64_t stream[7];    /* the stream state the current transition must carry */
    uint64_t answer[WORDS];  /* the answers to the current reset, transition or block projection */
};
extern struct law law;
#endif
