#ifndef LEANOS_BOOT_HANDOFF_DECODE_H
#define LEANOS_BOOT_HANDOFF_DECODE_H
#include <stdint.h>
#include "boundary-abi.h"

/* The Multiboot2 handoff copy and decoder of boot_allocate (#624): the first
 * C in LeanOS that reads memory the bootloader wrote.  It sits between the
 * Multiboot2 information and the generated exports of
 * LeanOS/BootMemoryMapStreaming.lean and
 * LeanOS/BootMemoryMapStreamAuthority.lean:
 *
 * - boot_handoff_extent checks the magic and the information's address,
 *   reads its total_size and checks the extent;
 * - boot_handoff_stream_copy replays every eight-byte chunk of the
 *   information through the generated handoff stream into the copy;
 * - boot_handoff_decode_projection runs the generated v5 decoder over the
 *   copy and builds the bounded projection from its typed entry events: it
 *   records each entry and projects it into the bitmaps;
 * - boot_handoff_decode_candidate runs the decoder again for one candidate
 *   frame;
 * - boot_handoff_project is boot_allocate's sequence after the extent: the
 *   copy, the projection and the decoder's acceptance.
 *
 * The physical read is a callback, so the identity-mapped load stays in the
 * kernel, and so is the record of each projection entry, which the kernel
 * stores in its own table.  The copy, the projection's bitmaps and the
 * decoder state are arguments.  The decoder state is two arrays of 41 words
 * that the transitions alternate between, so no state is ever copied.  Every
 * check returns a status, and the caller maps each status to the failure
 * reason of its check (boot/kernel.c: boot_handoff_require).  No function
 * here returns or copies a struct by value or uses a global, so QuickProof's
 * clightgen and VST take this header
 * (experiments/quickproof/boot-handoff-decode). */

#define BOOT_HANDOFF_MULTIBOOT2_MAGIC UINT32_C(0x36d76289)
#define BOOT_HANDOFF_PAGE_BYTES UINT32_C(4096)
/* The boot identity map ends at 16 MiB. */
#define BOOT_HANDOFF_ACCESSIBLE_LIMIT \
    (UINT32_C(16) * UINT32_C(1024) * UINT32_C(1024))
#define BOOT_HANDOFF_MAX_BYTES UINT32_C(65536)
#define BOOT_HANDOFF_MAX_WORDS (BOOT_HANDOFF_MAX_BYTES / UINT32_C(8))
/* The v5 decoder's state words, its projection entries (BootMemoryMap's
   maxEntries) and the projection's 64-bit bitmap blocks (4096 frames). */
#define BOOT_DECODE_WORDS 41
#define BOOT_PROJECTION_ENTRIES 256
#define BOOT_PROJECTION_BLOCKS 64

/* Record the canonical decoded memory-map entry of one entry event (its base,
   length and memory kind) in slot `slot`, below BOOT_PROJECTION_ENTRIES, of
   the caller's bounded table.  The kernel's record stores it in
   boot_projection_entries. */
typedef void (*boot_projection_record)(void *context, uint64_t slot,
                                       uint64_t base, uint64_t length,
                                       uint64_t kind);

/* The bounded projection: the record of its BOOT_PROJECTION_ENTRIES entries
   and three bitmaps of BOOT_PROJECTION_BLOCKS words.  The decoder fills the
   usable and blocked bitmaps and zeroes the reserved one, which the caller
   fills from the reservation manifest afterwards. */
struct boot_projection_storage {
    boot_projection_record record;
    void *context;
    uint64_t *usable;
    uint64_t *blocked;
    uint64_t *reserved;
};

/* The statuses, in the order of the checks.  The comment before each group
   names the failure reason boot_allocate gives for all of it. */
enum boot_handoff_status {
    BOOT_HANDOFF_OK,
    /* magic: not the Multiboot2 handoff magic. */
    BOOT_HANDOFF_MAGIC,
    /* pointer: the information's address is not 8-aligned, is below the
       first page or is not below the accessible limit. */
    BOOT_HANDOFF_POINTER_ALIGNMENT,
    BOOT_HANDOFF_POINTER_LOW,
    BOOT_HANDOFF_POINTER_HIGH,
    /* bounds: total_size is below 16, above 64 KiB, not a multiple of 8, or
       ends beyond the accessible limit. */
    BOOT_HANDOFF_BOUNDS_SMALL,
    BOOT_HANDOFF_BOUNDS_LARGE,
    BOOT_HANDOFF_BOUNDS_ALIGNMENT,
    BOOT_HANDOFF_BOUNDS_LIMIT,
    /* stream-init: the stream's reset answered word 0 (version) other than
       2, word 1 (status) other than 0, word 2 (error) other than 0, word 3
       (identity) other than the address, word 4 (extent) other than
       total_size or word 5 (next offset) other than 0. */
    BOOT_HANDOFF_STREAM_INIT_VERSION,
    BOOT_HANDOFF_STREAM_INIT_STATUS,
    BOOT_HANDOFF_STREAM_INIT_ERROR,
    BOOT_HANDOFF_STREAM_INIT_IDENTITY,
    BOOT_HANDOFF_STREAM_INIT_EXTENT,
    BOOT_HANDOFF_STREAM_INIT_OFFSET,
    /* stream-step: a chunk's transition answered word 0 other than 2, word 2
       other than 0, word 3 other than the address, word 4 other than
       total_size, word 5 other than the chunk's end, word 8 (count) other
       than 8, word 7 (exposed) other than the chunk, or word 1 other than 1
       at the last chunk and 0 before. */
    BOOT_HANDOFF_STREAM_STEP_VERSION,
    BOOT_HANDOFF_STREAM_STEP_ERROR,
    BOOT_HANDOFF_STREAM_STEP_IDENTITY,
    BOOT_HANDOFF_STREAM_STEP_EXTENT,
    BOOT_HANDOFF_STREAM_STEP_OFFSET,
    BOOT_HANDOFF_STREAM_STEP_COUNT,
    BOOT_HANDOFF_STREAM_STEP_EXPOSED,
    BOOT_HANDOFF_STREAM_STEP_STATUS,
    /* stream-incomplete: after the last chunk the stream is not complete or
       its next offset is not total_size. */
    BOOT_HANDOFF_STREAM_INCOMPLETE_STATUS,
    BOOT_HANDOFF_STREAM_INCOMPLETE_OFFSET,
    /* topology-handoff-length: the copy's length is not total_size. */
    BOOT_HANDOFF_COPY_LENGTH,
    /* decode-init: the decoder's reset answered word 0 other than 5, word 1
       or 2 other than 0, word 3 other than the address, word 4 other than
       total_size, or word 5 (offset), 16 (target frame), 18 (tag count) or
       30 (ACPI root status) other than 0. */
    BOOT_HANDOFF_DECODE_INIT_VERSION,
    BOOT_HANDOFF_DECODE_INIT_STATUS,
    BOOT_HANDOFF_DECODE_INIT_ERROR,
    BOOT_HANDOFF_DECODE_INIT_IDENTITY,
    BOOT_HANDOFF_DECODE_INIT_EXTENT,
    BOOT_HANDOFF_DECODE_INIT_OFFSET,
    BOOT_HANDOFF_DECODE_INIT_TARGET,
    BOOT_HANDOFF_DECODE_INIT_TAG_COUNT,
    BOOT_HANDOFF_DECODE_INIT_ROOT_STATUS,
    /* projection-entry-count: an entry event's entry count (word 11) is 0 or
       above BOOT_PROJECTION_ENTRIES. */
    BOOT_HANDOFF_PROJECTION_COUNT_ZERO,
    BOOT_HANDOFF_PROJECTION_COUNT_LARGE,
    /* projection-entry: an entry's projection into a bitmap block answered
       word 1 (status) other than 1 or word 2 (error) other than 0. */
    BOOT_HANDOFF_PROJECTION_ENTRY_STATUS,
    BOOT_HANDOFF_PROJECTION_ENTRY_ERROR,
    /* decode-incomplete: the decoder accepted every chunk but its final
       status (word 1) is not 1, its offset (word 5) not total_size or its
       phase (word 7) not 7 (done). */
    BOOT_HANDOFF_DECODE_INCOMPLETE_STATUS,
    BOOT_HANDOFF_DECODE_INCOMPLETE_OFFSET,
    BOOT_HANDOFF_DECODE_INCOMPLETE_PHASE,
    /* decode-rejected: the decoder's final status is not 1, or its error
       not 0. */
    BOOT_HANDOFF_DECODE_REJECTED_STATUS,
    BOOT_HANDOFF_DECODE_REJECTED_ERROR,
    /* authority-init: the candidate decoder's reset, with the checks of
       decode-init and the candidate as its target frame. */
    BOOT_HANDOFF_AUTHORITY_INIT_VERSION,
    BOOT_HANDOFF_AUTHORITY_INIT_STATUS,
    BOOT_HANDOFF_AUTHORITY_INIT_ERROR,
    BOOT_HANDOFF_AUTHORITY_INIT_IDENTITY,
    BOOT_HANDOFF_AUTHORITY_INIT_EXTENT,
    BOOT_HANDOFF_AUTHORITY_INIT_OFFSET,
    BOOT_HANDOFF_AUTHORITY_INIT_TARGET,
    BOOT_HANDOFF_AUTHORITY_INIT_TAG_COUNT,
    BOOT_HANDOFF_AUTHORITY_INIT_ROOT_STATUS,
    /* authority-rejected: the candidate decoder's final status is not 1, its
       error not 0, its offset not total_size, its phase not 7 or its target
       frame not the candidate. */
    BOOT_HANDOFF_AUTHORITY_REJECTED_STATUS,
    BOOT_HANDOFF_AUTHORITY_REJECTED_ERROR,
    BOOT_HANDOFF_AUTHORITY_REJECTED_OFFSET,
    BOOT_HANDOFF_AUTHORITY_REJECTED_PHASE,
    BOOT_HANDOFF_AUTHORITY_REJECTED_TARGET
};

/* Return the eight bytes of physical memory at the 8-aligned
 * `physical_address`, little-endian.  The kernel's read (an identity-mapped
 * load below BOOT_HANDOFF_ACCESSIBLE_LIMIT) is a trusted boundary. */
typedef uint64_t (*boot_handoff_read)(void *context, uint64_t physical_address);

/* Check the handoff's magic and the information's address, then read its
   total_size (the low half of its first eight bytes) and check the extent
   it declares: at least 16 bytes, at most 64 KiB, a multiple of 8, and
   ending within the accessible limit.  The address is read only after its
   checks pass.  On BOOT_HANDOFF_OK the extent is written to `total`, and
   nothing is written otherwise. */
static inline enum boot_handoff_status boot_handoff_extent(
        boot_handoff_read read, void *context, uint32_t magic,
        uint32_t info_address, uint32_t *total) {
    if (magic != BOOT_HANDOFF_MULTIBOOT2_MAGIC) return BOOT_HANDOFF_MAGIC;
    if ((info_address & 7u) != 0) return BOOT_HANDOFF_POINTER_ALIGNMENT;
    if (info_address < BOOT_HANDOFF_PAGE_BYTES) return BOOT_HANDOFF_POINTER_LOW;
    if (info_address >= BOOT_HANDOFF_ACCESSIBLE_LIMIT)
        return BOOT_HANDOFF_POINTER_HIGH;
    const uint32_t size = (uint32_t)read(context, info_address);
    if (size < 16u) return BOOT_HANDOFF_BOUNDS_SMALL;
    if (size > BOOT_HANDOFF_MAX_BYTES) return BOOT_HANDOFF_BOUNDS_LARGE;
    if ((size & 7u) != 0) return BOOT_HANDOFF_BOUNDS_ALIGNMENT;
    if (size > BOOT_HANDOFF_ACCESSIBLE_LIMIT - info_address)
        return BOOT_HANDOFF_BOUNDS_LIMIT;
    *total = size;
    return BOOT_HANDOFF_OK;
}

/* Physical memory access is the explicit TCB boundary.  The generated scalar
   transition binds every accepted eight-byte chunk to one aligned identity
   and extent, enforces exact offsets and terminal state, and exposes the word
   copied below only on success.  Each chunk's transition is asked words 0 to
   8 with one old state; the next chunk starts from words 0 to 6 (version,
   status, error, identity, extent, next offset, chain) of its answers.  Chunk
   k of the information goes to copy[k], which holds at least total / 8
   words, once its transition is accepted.  On BOOT_HANDOFF_OK the copy's
   length is written to `length`, and nothing is written otherwise. */
static inline enum boot_handoff_status boot_handoff_stream_copy(
        boot_handoff_read read, void *context, uint32_t magic,
        uint32_t info_address, uint32_t total, uint64_t *copy,
        uint32_t *length) {
    uint64_t state[7];
    for (uint64_t query = 0; query < 7; ++query)
        state[query] = leanos_boot_handoff_stream_init(
            magic, info_address, total, info_address, query);
    if (state[0] != 2) return BOOT_HANDOFF_STREAM_INIT_VERSION;
    if (state[1] != 0) return BOOT_HANDOFF_STREAM_INIT_STATUS;
    if (state[2] != 0) return BOOT_HANDOFF_STREAM_INIT_ERROR;
    if (state[3] != info_address) return BOOT_HANDOFF_STREAM_INIT_IDENTITY;
    if (state[4] != total) return BOOT_HANDOFF_STREAM_INIT_EXTENT;
    if (state[5] != 0) return BOOT_HANDOFF_STREAM_INIT_OFFSET;
    uint64_t answer[9];
    for (uint64_t offset = 0; offset < total; offset += 8) {
        const uint64_t chunk = read(context, (uint64_t)info_address + offset);
        const uint64_t terminal = offset + 8 == total;
        for (uint64_t query = 0; query < 9; ++query)
            answer[query] = leanos_boot_handoff_stream_step(
                state[0], state[1], state[2], state[3], state[4], state[5],
                state[6], info_address, offset, 8, chunk, terminal, query);
        if (answer[0] != 2) return BOOT_HANDOFF_STREAM_STEP_VERSION;
        if (answer[2] != 0) return BOOT_HANDOFF_STREAM_STEP_ERROR;
        if (answer[3] != info_address) return BOOT_HANDOFF_STREAM_STEP_IDENTITY;
        if (answer[4] != total) return BOOT_HANDOFF_STREAM_STEP_EXTENT;
        if (answer[5] != offset + 8) return BOOT_HANDOFF_STREAM_STEP_OFFSET;
        if (answer[8] != 8) return BOOT_HANDOFF_STREAM_STEP_COUNT;
        if (answer[7] != chunk) return BOOT_HANDOFF_STREAM_STEP_EXPOSED;
        if (answer[1] != (terminal ? 1u : 0u))
            return BOOT_HANDOFF_STREAM_STEP_STATUS;
        copy[offset / 8] = answer[7];
        for (uint64_t word = 0; word < 7; ++word)
            state[word] = answer[word];
    }
    if (state[1] != 1) return BOOT_HANDOFF_STREAM_INCOMPLETE_STATUS;
    if (state[5] != total) return BOOT_HANDOFF_STREAM_INCOMPLETE_OFFSET;
    *length = total;
    return BOOT_HANDOFF_OK;
}

/* The decoder's reset for target frame `target`: words 0 to 40, into
   `state`. */
static inline void boot_decode_reset(
        uint32_t magic, uint32_t info_address, uint32_t total, uint64_t target,
        uint64_t *state) {
    for (uint64_t query = 0; query < BOOT_DECODE_WORDS; ++query)
        state[query] = leanos_boot_decode_init_v5(
            magic, info_address, total, target, query);
}

/* One decoder transition over `chunk`, the eight bytes at `offset` of the
   copy: words 0 to 40 of the transition of `state`, into `next`.  Every
   word is asked with the same old state, its words 0 to 18 and 23 to 38
   (words 19 to 22 are the last transition's entry event and words 39 and
   40 its ACPI root selection, which the transition does not take). */
static inline void boot_decode_transition(
        const uint64_t *state, uint32_t info_address, uint64_t offset,
        uint64_t chunk, uint64_t terminal, uint64_t *next) {
    for (uint64_t query = 0; query < BOOT_DECODE_WORDS; ++query)
        next[query] = leanos_boot_decode_step_v5(
            state[0], state[1], state[2], state[3], state[4], state[5],
            state[6], state[7], state[8], state[9], state[10], state[11],
            state[12], state[13], state[14], state[15], state[16], state[17],
            state[18], state[23], state[24], state[25], state[26], state[27],
            state[28], state[29], state[30], state[31], state[32], state[33],
            state[34], state[35], state[36], state[37], state[38],
            info_address, offset, chunk, terminal, query);
}

/* Parse the immutable copy exactly once.  The generated transition emits each
   canonical decoded entry on its accepting type step; C only retains those
   typed events and the generated 4096-frame bounded projection.

   The copy holds total / 8 words.  The decoder's reset goes to states[0],
   and each transition's answers to the other of the two states, so the
   decoder's state is always states[current].  Decoding stops at the first
   transition that answers a nonzero error (word 2).  An accepted transition
   with an entry event (word 19 is 1) records the entry (words 20 to 22) in
   slot (word 11) - 1, once that is below BOOT_PROJECTION_ENTRIES, and
   projects it into each bitmap block in order.  On BOOT_HANDOFF_OK, whether
   or not the decoder rejected the handoff, the index of the decoder's state
   is written to `current`, and nothing is written otherwise. */
static inline enum boot_handoff_status boot_handoff_decode_projection(
        uint32_t magic, uint32_t info_address, uint32_t total,
        const uint64_t *info, const struct boot_projection_storage *projection,
        uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current) {
    for (uint64_t block = 0; block < BOOT_PROJECTION_BLOCKS; ++block) {
        projection->usable[block] = 0;
        projection->blocked[block] = 0;
        projection->reserved[block] = 0;
    }
    uint32_t at = 0;
    boot_decode_reset(magic, info_address, total, 0, states[0]);
    if (states[0][0] != 5) return BOOT_HANDOFF_DECODE_INIT_VERSION;
    if (states[0][1] != 0) return BOOT_HANDOFF_DECODE_INIT_STATUS;
    if (states[0][2] != 0) return BOOT_HANDOFF_DECODE_INIT_ERROR;
    if (states[0][3] != info_address) return BOOT_HANDOFF_DECODE_INIT_IDENTITY;
    if (states[0][4] != total) return BOOT_HANDOFF_DECODE_INIT_EXTENT;
    if (states[0][5] != 0) return BOOT_HANDOFF_DECODE_INIT_OFFSET;
    if (states[0][16] != 0) return BOOT_HANDOFF_DECODE_INIT_TARGET;
    if (states[0][18] != 0) return BOOT_HANDOFF_DECODE_INIT_TAG_COUNT;
    if (states[0][30] != 0) return BOOT_HANDOFF_DECODE_INIT_ROOT_STATUS;
    for (uint64_t offset = 0; offset < total; offset += 8) {
        const uint64_t terminal = offset + 8 == total;
        boot_decode_transition(states[at], info_address, offset,
                               info[offset / 8], terminal, states[1u - at]);
        at = 1u - at;
        const uint64_t *state = states[at];
        if (state[2] != 0) break;
        if (state[19] == 1) {
            if (state[11] == 0) return BOOT_HANDOFF_PROJECTION_COUNT_ZERO;
            if (state[11] > BOOT_PROJECTION_ENTRIES)
                return BOOT_HANDOFF_PROJECTION_COUNT_LARGE;
            projection->record(projection->context, state[11] - 1, state[20],
                               state[21], state[22]);
            for (uint64_t block = 0; block < BOOT_PROJECTION_BLOCKS; ++block) {
                const uint64_t status = leanos_boot_projection_entry(
                    state[20], state[21], state[22], block,
                    projection->usable[block], projection->blocked[block], 1);
                const uint64_t error = leanos_boot_projection_entry(
                    state[20], state[21], state[22], block,
                    projection->usable[block], projection->blocked[block], 2);
                const uint64_t usable = leanos_boot_projection_entry(
                    state[20], state[21], state[22], block,
                    projection->usable[block], projection->blocked[block], 3);
                const uint64_t blocked = leanos_boot_projection_entry(
                    state[20], state[21], state[22], block,
                    projection->usable[block], projection->blocked[block], 4);
                if (status != 1) return BOOT_HANDOFF_PROJECTION_ENTRY_STATUS;
                if (error != 0) return BOOT_HANDOFF_PROJECTION_ENTRY_ERROR;
                projection->usable[block] = usable;
                projection->blocked[block] = blocked;
            }
        }
    }
    if (states[at][2] == 0) {
        if (states[at][1] != 1) return BOOT_HANDOFF_DECODE_INCOMPLETE_STATUS;
        if (states[at][5] != total) return BOOT_HANDOFF_DECODE_INCOMPLETE_OFFSET;
        if (states[at][7] != 7) return BOOT_HANDOFF_DECODE_INCOMPLETE_PHASE;
    }
    *current = at;
    return BOOT_HANDOFF_OK;
}

/* Re-run the same generated decoder for the candidate selected from the
   bounded projection.  This scalar terminal state is the authorization gate:
   caller-owned projection storage may suggest a candidate, but cannot grant
   usable-frame or non-overlap authority.

   The copy, the two states and `current` are as for
   boot_handoff_decode_projection, with `candidate` as the target frame and
   no projection.  It returns BOOT_HANDOFF_OK only when the decoder accepted
   the handoff for the candidate: its final status is 1, its error 0, its
   offset total_size, its phase 7 and its target frame the candidate. */
static inline enum boot_handoff_status boot_handoff_decode_candidate(
        uint32_t magic, uint32_t info_address, uint32_t total,
        uint64_t candidate, const uint64_t *info,
        uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current) {
    uint32_t at = 0;
    boot_decode_reset(magic, info_address, total, candidate, states[0]);
    if (states[0][0] != 5) return BOOT_HANDOFF_AUTHORITY_INIT_VERSION;
    if (states[0][1] != 0) return BOOT_HANDOFF_AUTHORITY_INIT_STATUS;
    if (states[0][2] != 0) return BOOT_HANDOFF_AUTHORITY_INIT_ERROR;
    if (states[0][3] != info_address)
        return BOOT_HANDOFF_AUTHORITY_INIT_IDENTITY;
    if (states[0][4] != total) return BOOT_HANDOFF_AUTHORITY_INIT_EXTENT;
    if (states[0][5] != 0) return BOOT_HANDOFF_AUTHORITY_INIT_OFFSET;
    if (states[0][16] != candidate) return BOOT_HANDOFF_AUTHORITY_INIT_TARGET;
    if (states[0][18] != 0) return BOOT_HANDOFF_AUTHORITY_INIT_TAG_COUNT;
    if (states[0][30] != 0) return BOOT_HANDOFF_AUTHORITY_INIT_ROOT_STATUS;
    for (uint64_t offset = 0; offset < total; offset += 8) {
        const uint64_t terminal = offset + 8 == total;
        boot_decode_transition(states[at], info_address, offset,
                               info[offset / 8], terminal, states[1u - at]);
        at = 1u - at;
        if (states[at][2] != 0) break;
    }
    if (states[at][1] != 1) return BOOT_HANDOFF_AUTHORITY_REJECTED_STATUS;
    if (states[at][2] != 0) return BOOT_HANDOFF_AUTHORITY_REJECTED_ERROR;
    if (states[at][5] != total) return BOOT_HANDOFF_AUTHORITY_REJECTED_OFFSET;
    if (states[at][7] != 7) return BOOT_HANDOFF_AUTHORITY_REJECTED_PHASE;
    if (states[at][16] != candidate)
        return BOOT_HANDOFF_AUTHORITY_REJECTED_TARGET;
    *current = at;
    return BOOT_HANDOFF_OK;
}

/* boot_allocate's sequence after boot_handoff_extent: copy the information
   through the generated stream into `copy`, which holds
   BOOT_HANDOFF_MAX_WORDS words, then decode the copy into the projection
   and the two states, and accept only a handoff the decoder accepted.
   `total` is the extent boot_handoff_extent wrote.  On BOOT_HANDOFF_OK the
   index of the decoder's final state is written to `current`, and nothing
   is written otherwise. */
static inline enum boot_handoff_status boot_handoff_project(
        boot_handoff_read read, void *context, uint32_t magic,
        uint32_t info_address, uint32_t total, uint64_t *copy,
        const struct boot_projection_storage *projection,
        uint64_t states[2][BOOT_DECODE_WORDS], uint32_t *current) {
    uint32_t length = 0;
    enum boot_handoff_status status = boot_handoff_stream_copy(
        read, context, magic, info_address, total, copy, &length);
    if (status != BOOT_HANDOFF_OK) return status;
    if (length != total) return BOOT_HANDOFF_COPY_LENGTH;
    uint32_t decoded = 0;
    status = boot_handoff_decode_projection(
        magic, info_address, total, copy, projection, states, &decoded);
    if (status != BOOT_HANDOFF_OK) return status;
    if (states[decoded][1] != 1) return BOOT_HANDOFF_DECODE_REJECTED_STATUS;
    if (states[decoded][2] != 0) return BOOT_HANDOFF_DECODE_REJECTED_ERROR;
    *current = decoded;
    return BOOT_HANDOFF_OK;
}

#endif
