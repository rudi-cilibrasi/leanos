/* Law handoff_decode_exact.  The physical read, the projection's record and the five Lean exports the header calls
   are this harness's: a bootloader whose memory answers every read with any eight bytes, a different value each
   time (so the size read and chunk 0 may disagree), and an adversarial Lean that answers every call with any 64-bit
   value, a different one each time; both, and the record, check every call.  For every magic and information
   address (any 32-bit values), every candidate (any 64-bit value), a copy of BOOT_HANDOFF_MAX_WORDS (8192) words
   (for an allocation or a copy), three bitmaps of 64 words, two decoder states of 41 words and three records
   (the extent, the copy's length and the state's index), every object holding any values, main calls one entry
   point of include/boot_handoff_decode.h (patch/handoff_unit.c), and it behaves as follows.  Statuses are those
   of the header without the prefix BOOT_HANDOFF_; word q of a reset, transition or block projection is the answer
   to its call for query q; chunk k is the eight bytes at offset 8k, the last one when 8k + 8 is the extent.
     - Allocation (boot_handoff_extent, then, when it returns OK, boot_handoff_project with the extent it wrote, as
       boot_allocate calls them): it returns MAGIC unless the magic is 0x36d76289, then POINTER_ALIGNMENT,
       POINTER_LOW or POINTER_HIGH when the address is not a multiple of 8, is below 4096 or is not below 16 MiB,
       without a call.  Otherwise it reads the eight bytes at the address once; with their low 32 bits as the extent
       T, it returns BOUNDS_SMALL, BOUNDS_LARGE, BOUNDS_ALIGNMENT or BOUNDS_LIMIT when T is below 16, above 65536,
       not a multiple of 8, or above 16 MiB minus the address, without a further call.  Otherwise it writes T to the
       extent record and runs the copy below with T, then, when the copy returns OK, the decoder below with a
       projection and the copy as the words decoded.  When the decoder's run ends with OK it returns
       DECODE_REJECTED_STATUS unless the final state's word 1 is 1, then DECODE_REJECTED_ERROR unless its word 2 is
       0; else OK, writing the index of the final state to the state record.
     - Copy (boot_handoff_stream_copy, alone with any extent T that is a multiple of 8 up to 65536, or in an
       allocation): it calls the stream reset 7 times, for words 0..6 in order, each with the magic, the address, T
       and the address again, and returns STREAM_INIT_VERSION, _STATUS, _ERROR, _IDENTITY, _EXTENT or _OFFSET, the
       first that applies, unless words 0..5 are 2, 0, 0, the address, T and 0.  Then for each chunk k in order it
       reads the eight bytes at the address + 8k once and calls the stream transition 9 times, for words 0..8 in
       order, each with the carried state (words 0..6 of the reset, then of the previous chunk's answers), the
       address, 8k, 8, the chunk as read, and 1 for the last chunk, 0 before.  It goes on only when the answers
       accept the chunk: word 0 is 2, word 2 is 0, word 3 the address, word 4 T, word 5 8k + 8, word 8 is 8, word 7
       the chunk, and word 1 is 1 at the last chunk and 0 before; at the first chunk they do not accept it returns
       STREAM_STEP_VERSION, _ERROR, _IDENTITY, _EXTENT, _OFFSET, _COUNT, _EXPOSED or _STATUS, the first that
       applies.  An accepted chunk k is written to word k of the copy.  After the last chunk (at once when T is 0)
       it returns STREAM_INCOMPLETE_STATUS unless the carried word 1 is 1, then STREAM_INCOMPLETE_OFFSET unless the
       carried word 5 is T; else OK (alone, writing T to the length record).
     - Decoder (boot_handoff_decode_projection with a projection and target 0, or boot_handoff_decode_candidate with
       the candidate as target; alone, each with any extent T that is a multiple of 8 up to 65536 and an object of
       T / 8 words holding any values as the words decoded): with a projection it first writes 0 to every word of
       the three bitmaps.  It calls the decoder reset 41 times, for words 0..40 in order, each with the magic, the
       address, T and the target, and writes the answers to state 0, the current state.  It returns INIT_VERSION,
       INIT_STATUS, INIT_ERROR, INIT_IDENTITY, INIT_EXTENT, INIT_OFFSET, INIT_TARGET, INIT_TAG_COUNT or
       INIT_ROOT_STATUS (prefixed DECODE_ with a projection and AUTHORITY_ for a candidate), the first that
       applies, unless words 0..5 are 5, 0, 0, the address, T and 0, word 16 is the target and words 18 and 30 are
       0.  Then for each chunk k in order it calls the decoder transition 41 times, for words 0..40 in order, each
       with words 0..18 and 23..38 of the current state, the address, 8k, word k of the words decoded, and 1 for
       the last chunk, 0 before; it writes the answers to the other of states 0 and 1, which becomes the current
       state.  It stops at the first transition whose word 2 is not 0.  With a projection, any other transition
       whose word 19 is 1 is an entry event: it returns PROJECTION_COUNT_ZERO when word 11 is 0 and
       PROJECTION_COUNT_LARGE when it is above 256; otherwise it calls the record once with slot word 11 - 1 (below
       256) and words 20, 21 and 22, then for each block b of 0..63 in order calls the block projection 4 times,
       for words 1..4 in order, each with words 20, 21, 22, b and the current words b of the usable and blocked
       bitmaps, and returns PROJECTION_ENTRY_STATUS unless word 1 is 1, then PROJECTION_ENTRY_ERROR unless word 2
       is 0, else writes words 3 and 4 to word b of the usable and blocked bitmaps.  After the last chunk or the
       stop, with the current state: with a projection it returns DECODE_INCOMPLETE_STATUS, _OFFSET or _PHASE, the
       first that applies, when word 2 is 0 and word 1 is not 1, word 5 not T or word 7 not 7; for a candidate it
       returns AUTHORITY_REJECTED_STATUS, _ERROR, _OFFSET, _PHASE or _TARGET, the first that applies, unless word 1
       is 1, word 2 is 0, word 5 is T, word 7 is 7 and word 16 the candidate.  Else it returns OK (alone, writing
       the index of the current state to the state record), whether or not a projection's decoder stopped.
     - Calls and writes: no function makes a read or a call but those above, in that order, and none after the
       check that decides its status.  It writes only the copy's words of the accepted chunks, the bitmaps, the
       two states and, on OK only, its record (an allocation also the extent record once the bounds accept T);
       every other word of every object keeps its value, and the words a decoder alone reads are unchanged.
   So no bootloader and no Lean answer can make the header read anything but the information's first eight bytes
   and, once the bounds accept its extent, each of its chunks once and in order; copy a chunk the stream did not
   expose; write outside the copy, the bitmaps or the two states, or record an entry outside the 256 slots; skip a
   chunk or a block; ask a transition about another state, offset or chunk than the ones it carries; go on after a
   rejected transition; or accept a handoff, or a candidate, the decoder did not accept.  The bootloader, the record
   and the Lean exports below are the reference: they keep the state the header must carry and check every call
   against it, and the law's model (harness/handoff_decode_exact.h) keeps its own copy of what memory must hold;
   main compares the status, the copy, the bitmaps, the states and the records.  Not claimed: termination (partial
   correctness; every loop is bounded); what the Lean answers mean (the BootMemoryMapStreaming and
   BootMemoryMapStreamAuthority theorems); the physical read and the record themselves; the kernel's use of the
   decoded words after the decoder. */
#include <stdlib.h>
#include "quickproof.h"
#include "handoff_decode_exact.h"

struct law law;

static uint64_t any_u64(void) {
    uint64_t hi = nondet_u32();
    uint64_t lo = nondet_u32();
    return hi << 32 | lo;
}

static void stop(struct law *m, uint32_t verdict) {
    m->expect = EXPECT_NOTHING;
    m->verdict = verdict;
}

/* The copy's turn: the stream reset. */
static void begin_stream(struct law *m) {
    m->word = 0;
    m->expect = EXPECT_STREAM_INIT;
}

/* The decoder's turn: with a projection its bitmaps are zeroed first; then the reset. */
static void begin_decode(struct law *m) {
    if (m->projection) {
        for (uint32_t b = 0; b < BLOCKS; ++b) {
            m->usable_expect[b] = 0;
            m->blocked_expect[b] = 0;
            m->reserved_expect[b] = 0;
        }
    }
    m->word = 0;
    m->expect = EXPECT_DECODE_INIT;
}

/* The stream accepted every chunk before chunk k: read chunk k, or finish the copy. */
static void begin_chunk(struct law *m, uint64_t k) {
    if (8 * k < m->total) {
        m->chunk = k;
        m->expect = EXPECT_CHUNK;
        return;
    }
    if (m->stream[1] != 1) {
        stop(m, BOOT_HANDOFF_STREAM_INCOMPLETE_STATUS);
        return;
    }
    if (m->stream[5] != m->total) {
        stop(m, BOOT_HANDOFF_STREAM_INCOMPLETE_OFFSET);
        return;
    }
    if (m->call == CALL_COPY)
        stop(m, BOOT_HANDOFF_OK);
    else
        begin_decode(m);
}

/* The decoder stopped (its state's error word is not 0) or ran out of chunks: its final checks. */
static void decode_done(struct law *m) {
    const uint64_t *s = m->states_expect[m->at];
    if (!m->projection) {
        if (s[1] != 1) stop(m, BOOT_HANDOFF_AUTHORITY_REJECTED_STATUS);
        else if (s[2] != 0) stop(m, BOOT_HANDOFF_AUTHORITY_REJECTED_ERROR);
        else if (s[5] != m->total) stop(m, BOOT_HANDOFF_AUTHORITY_REJECTED_OFFSET);
        else if (s[7] != 7) stop(m, BOOT_HANDOFF_AUTHORITY_REJECTED_PHASE);
        else if (s[16] != m->candidate) stop(m, BOOT_HANDOFF_AUTHORITY_REJECTED_TARGET);
        else stop(m, BOOT_HANDOFF_OK);
        return;
    }
    if (s[2] == 0) {
        if (s[1] != 1) {
            stop(m, BOOT_HANDOFF_DECODE_INCOMPLETE_STATUS);
            return;
        }
        if (s[5] != m->total) {
            stop(m, BOOT_HANDOFF_DECODE_INCOMPLETE_OFFSET);
            return;
        }
        if (s[7] != 7) {
            stop(m, BOOT_HANDOFF_DECODE_INCOMPLETE_PHASE);
            return;
        }
    }
    if (m->call == CALL_ALLOCATE && s[1] != 1) stop(m, BOOT_HANDOFF_DECODE_REJECTED_STATUS);
    else if (m->call == CALL_ALLOCATE && s[2] != 0) stop(m, BOOT_HANDOFF_DECODE_REJECTED_ERROR);
    else stop(m, BOOT_HANDOFF_OK);
}

/* The decoder accepted every transition before chunk k: decode chunk k, or finish. */
static void begin_transition(struct law *m, uint64_t k) {
    if (8 * k < m->total) {
        m->chunk = k;
        m->value = m->info_expect[k];
        m->word = 0;
        m->expect = EXPECT_DECODE_STEP;
        return;
    }
    decode_done(m);
}

/* The bootloader: any eight bytes at every read, a different value each time. */
static uint64_t bootloader_read(void *context, uint64_t physical_address) {
    struct law *m = &law;
    qp_assert(context == (void *)m);
    qp_assert(m->expect == EXPECT_SIZE || m->expect == EXPECT_CHUNK);
    uint64_t v = any_u64();
    if (m->expect == EXPECT_SIZE) {
        qp_assert(physical_address == m->address);
        uint32_t size = (uint32_t)v;
        if (size < 16) {
            stop(m, BOOT_HANDOFF_BOUNDS_SMALL);
        } else if (size > BOOT_HANDOFF_MAX_BYTES) {
            stop(m, BOOT_HANDOFF_BOUNDS_LARGE);
        } else if ((size & 7) != 0) {
            stop(m, BOOT_HANDOFF_BOUNDS_ALIGNMENT);
        } else if (size > BOOT_HANDOFF_ACCESSIBLE_LIMIT - m->address) {
            stop(m, BOOT_HANDOFF_BOUNDS_LIMIT);
        } else {
            m->total = size;
            m->extent_ok = 1;
            begin_stream(m);
        }
        return v;
    }
    qp_assert(physical_address == (uint64_t)m->address + 8 * m->chunk);
    m->value = v;
    m->word = 0;
    m->expect = EXPECT_STREAM_STEP;
    return v;
}

uint64_t leanos_boot_handoff_stream_init(uint64_t magic, uint64_t info_address, uint64_t total_bytes,
                                         uint64_t stream_identity, uint64_t query) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_STREAM_INIT && query == m->word);
    qp_assert(magic == m->magic && info_address == m->address && total_bytes == m->total &&
              stream_identity == m->address);
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < 6) {
        m->word = m->word + 1;
        return v;
    }
    for (uint32_t i = 0; i < 7; ++i)
        m->stream[i] = m->answer[i];
    if (m->stream[0] != 2) stop(m, BOOT_HANDOFF_STREAM_INIT_VERSION);
    else if (m->stream[1] != 0) stop(m, BOOT_HANDOFF_STREAM_INIT_STATUS);
    else if (m->stream[2] != 0) stop(m, BOOT_HANDOFF_STREAM_INIT_ERROR);
    else if (m->stream[3] != m->address) stop(m, BOOT_HANDOFF_STREAM_INIT_IDENTITY);
    else if (m->stream[4] != m->total) stop(m, BOOT_HANDOFF_STREAM_INIT_EXTENT);
    else if (m->stream[5] != 0) stop(m, BOOT_HANDOFF_STREAM_INIT_OFFSET);
    else begin_chunk(m, 0);
    return v;
}

uint64_t leanos_boot_handoff_stream_step(uint64_t version, uint64_t status, uint64_t error,
                                         uint64_t bound_identity, uint64_t bound_extent, uint64_t next_offset,
                                         uint64_t chain, uint64_t stream_identity, uint64_t offset,
                                         uint64_t count, uint64_t chunk, uint64_t terminal, uint64_t query) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_STREAM_STEP && query == m->word);
    qp_assert(version == m->stream[0] && status == m->stream[1] && error == m->stream[2] &&
              bound_identity == m->stream[3] && bound_extent == m->stream[4] && next_offset == m->stream[5] &&
              chain == m->stream[6]);
    uint64_t end = 8 * m->chunk + 8;
    uint64_t last = end == m->total;
    qp_assert(stream_identity == m->address && offset == 8 * m->chunk && count == 8 && chunk == m->value &&
              terminal == last);
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < 8) {
        m->word = m->word + 1;
        return v;
    }
    const uint64_t *a = m->answer;
    if (a[0] != 2) stop(m, BOOT_HANDOFF_STREAM_STEP_VERSION);
    else if (a[2] != 0) stop(m, BOOT_HANDOFF_STREAM_STEP_ERROR);
    else if (a[3] != m->address) stop(m, BOOT_HANDOFF_STREAM_STEP_IDENTITY);
    else if (a[4] != m->total) stop(m, BOOT_HANDOFF_STREAM_STEP_EXTENT);
    else if (a[5] != end) stop(m, BOOT_HANDOFF_STREAM_STEP_OFFSET);
    else if (a[8] != 8) stop(m, BOOT_HANDOFF_STREAM_STEP_COUNT);
    else if (a[7] != m->value) stop(m, BOOT_HANDOFF_STREAM_STEP_EXPOSED);
    else if (a[1] != last) stop(m, BOOT_HANDOFF_STREAM_STEP_STATUS);
    else {
        m->copy_expect[m->chunk] = m->value;
        for (uint32_t i = 0; i < 7; ++i)
            m->stream[i] = a[i];
        begin_chunk(m, m->chunk + 1);
    }
    return v;
}

uint64_t leanos_boot_decode_init_v5(uint64_t magic, uint64_t address, uint64_t extent, uint64_t target,
                                    uint64_t query) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_DECODE_INIT && query == m->word);
    qp_assert(magic == m->magic && address == m->address && extent == m->total && target == m->candidate);
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < WORDS - 1) {
        m->word = m->word + 1;
        return v;
    }
    for (uint32_t i = 0; i < WORDS; ++i)
        m->states_expect[0][i] = m->answer[i];
    m->at = 0;
    const uint64_t *s = m->states_expect[0];
    uint32_t p = m->projection;
    if (s[0] != 5) stop(m, p ? BOOT_HANDOFF_DECODE_INIT_VERSION : BOOT_HANDOFF_AUTHORITY_INIT_VERSION);
    else if (s[1] != 0) stop(m, p ? BOOT_HANDOFF_DECODE_INIT_STATUS : BOOT_HANDOFF_AUTHORITY_INIT_STATUS);
    else if (s[2] != 0) stop(m, p ? BOOT_HANDOFF_DECODE_INIT_ERROR : BOOT_HANDOFF_AUTHORITY_INIT_ERROR);
    else if (s[3] != m->address)
        stop(m, p ? BOOT_HANDOFF_DECODE_INIT_IDENTITY : BOOT_HANDOFF_AUTHORITY_INIT_IDENTITY);
    else if (s[4] != m->total) stop(m, p ? BOOT_HANDOFF_DECODE_INIT_EXTENT : BOOT_HANDOFF_AUTHORITY_INIT_EXTENT);
    else if (s[5] != 0) stop(m, p ? BOOT_HANDOFF_DECODE_INIT_OFFSET : BOOT_HANDOFF_AUTHORITY_INIT_OFFSET);
    else if (s[16] != m->candidate)
        stop(m, p ? BOOT_HANDOFF_DECODE_INIT_TARGET : BOOT_HANDOFF_AUTHORITY_INIT_TARGET);
    else if (s[18] != 0) stop(m, p ? BOOT_HANDOFF_DECODE_INIT_TAG_COUNT : BOOT_HANDOFF_AUTHORITY_INIT_TAG_COUNT);
    else if (s[30] != 0)
        stop(m, p ? BOOT_HANDOFF_DECODE_INIT_ROOT_STATUS : BOOT_HANDOFF_AUTHORITY_INIT_ROOT_STATUS);
    else begin_transition(m, 0);
    return v;
}

uint64_t leanos_boot_decode_step_v5(
        uint64_t s0, uint64_t s1, uint64_t s2, uint64_t s3, uint64_t s4, uint64_t s5, uint64_t s6, uint64_t s7,
        uint64_t s8, uint64_t s9, uint64_t s10, uint64_t s11, uint64_t s12, uint64_t s13, uint64_t s14,
        uint64_t s15, uint64_t s16, uint64_t s17, uint64_t s18, uint64_t s23, uint64_t s24, uint64_t s25,
        uint64_t s26, uint64_t s27, uint64_t s28, uint64_t s29, uint64_t s30, uint64_t s31, uint64_t s32,
        uint64_t s33, uint64_t s34, uint64_t s35, uint64_t s36, uint64_t s37, uint64_t s38,
        uint64_t stream_identity, uint64_t stream_offset, uint64_t chunk, uint64_t terminal, uint64_t query) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_DECODE_STEP && query == m->word);
    const uint64_t *o = m->states_expect[m->at];
    qp_assert(s0 == o[0] && s1 == o[1] && s2 == o[2] && s3 == o[3] && s4 == o[4] && s5 == o[5] && s6 == o[6] &&
              s7 == o[7] && s8 == o[8] && s9 == o[9] && s10 == o[10] && s11 == o[11] && s12 == o[12] &&
              s13 == o[13] && s14 == o[14] && s15 == o[15] && s16 == o[16] && s17 == o[17] && s18 == o[18]);
    qp_assert(s23 == o[23] && s24 == o[24] && s25 == o[25] && s26 == o[26] && s27 == o[27] && s28 == o[28] &&
              s29 == o[29] && s30 == o[30] && s31 == o[31] && s32 == o[32] && s33 == o[33] && s34 == o[34] &&
              s35 == o[35] && s36 == o[36] && s37 == o[37] && s38 == o[38]);
    uint64_t last = 8 * m->chunk + 8 == m->total;
    qp_assert(stream_identity == m->address && stream_offset == 8 * m->chunk && chunk == m->value &&
              terminal == last);
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < WORDS - 1) {
        m->word = m->word + 1;
        return v;
    }
    uint32_t next = 1 - m->at;
    for (uint32_t i = 0; i < WORDS; ++i)
        m->states_expect[next][i] = m->answer[i];
    m->at = next;
    const uint64_t *s = m->states_expect[next];
    if (s[2] != 0) {
        decode_done(m);
    } else if (m->projection && s[19] == 1) {
        if (s[11] == 0) {
            stop(m, BOOT_HANDOFF_PROJECTION_COUNT_ZERO);
        } else if (s[11] > ENTRIES) {
            stop(m, BOOT_HANDOFF_PROJECTION_COUNT_LARGE);
        } else {
            m->expect = EXPECT_RECORD;
        }
    } else {
        begin_transition(m, m->chunk + 1);
    }
    return v;
}

/* The record of the projection's entries: checks that it gets the event's slot and entry, then the event's blocks
   are next. */
static void projection_record(void *context, uint64_t slot, uint64_t base, uint64_t length, uint64_t kind) {
    struct law *m = &law;
    qp_assert(context == (void *)m && m->expect == EXPECT_RECORD);
    const uint64_t *s = m->states_expect[m->at];
    qp_assert(slot == s[11] - 1 && slot < ENTRIES && base == s[20] && length == s[21] && kind == s[22]);
    m->records = m->records + 1;
    m->block = 0;
    m->word = 0;
    m->expect = EXPECT_ENTRY;
}

uint64_t leanos_boot_projection_entry(uint64_t base, uint64_t length, uint64_t kind_word, uint64_t block,
                                      uint64_t usable, uint64_t blocked, uint64_t query) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_ENTRY && query == m->word + 1);
    const uint64_t *s = m->states_expect[m->at];
    qp_assert(base == s[20] && length == s[21] && kind_word == s[22] && block == m->block &&
              usable == m->usable_expect[m->block] && blocked == m->blocked_expect[m->block]);
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < 3) {
        m->word = m->word + 1;
        return v;
    }
    if (m->answer[0] != 1) {
        stop(m, BOOT_HANDOFF_PROJECTION_ENTRY_STATUS);
    } else if (m->answer[1] != 0) {
        stop(m, BOOT_HANDOFF_PROJECTION_ENTRY_ERROR);
    } else {
        m->usable_expect[m->block] = m->answer[2];
        m->blocked_expect[m->block] = m->answer[3];
        if (m->block + 1 < BLOCKS) {
            m->block = m->block + 1;
            m->word = 0;
        } else {
            begin_transition(m, m->chunk + 1);
        }
    }
    return v;
}

int main(void) {
    struct law *m = &law;
    m->call = nondet_u32() % 4;
    m->magic = nondet_u32();
    m->address = nondet_u32();
    m->total = nondet_u32();
    m->candidate = any_u64();
    /* The extent of a copy or a decoding alone: any multiple of 8 up to 64 KiB.  An allocation's comes from its
       size read. */
    if (m->call != CALL_ALLOCATE && (m->total > BOOT_HANDOFF_MAX_BYTES || (m->total & 7) != 0))
        return 0;
    if (m->call != CALL_CANDIDATE)
        m->candidate = 0;
    m->projection = m->call == CALL_ALLOCATE || m->call == CALL_PROJECTION;
    /* The storage, each object holding any values: the copy of BOOT_HANDOFF_MAX_WORDS words (for an allocation or a
       copy), the words a decoding alone reads (total / 8 of them), the projection's bitmaps, the decoder's two
       states and the three records a function may write. */
    uint32_t copy_words = m->call == CALL_ALLOCATE || m->call == CALL_COPY ? COPY_WORDS : 0;
    uint64_t *copy = malloc(copy_words * sizeof(uint64_t));
    uint64_t *copy_expect = malloc(copy_words * sizeof(uint64_t));
    uint32_t info_words = m->call == CALL_ALLOCATE ? 0 : m->total / 8;
    uint64_t *info = malloc(info_words * sizeof(uint64_t));
    uint64_t *info_expect = malloc(info_words * sizeof(uint64_t));
    uint64_t *usable = malloc(BLOCKS * sizeof(uint64_t));
    uint64_t *blocked = malloc(BLOCKS * sizeof(uint64_t));
    uint64_t *reserved = malloc(BLOCKS * sizeof(uint64_t));
    uint64_t (*states)[WORDS] = malloc(2 * WORDS * sizeof(uint64_t));
    if (copy == NULL || copy_expect == NULL || info == NULL || info_expect == NULL || usable == NULL ||
        blocked == NULL || reserved == NULL || states == NULL)
        return 0;
    for (uint32_t i = 0; i < copy_words; ++i) {
        copy[i] = any_u64();
        copy_expect[i] = copy[i];
    }
    for (uint32_t i = 0; i < info_words; ++i) {
        info[i] = any_u64();
        info_expect[i] = info[i];
    }
    for (uint32_t b = 0; b < BLOCKS; ++b) {
        usable[b] = any_u64();
        blocked[b] = any_u64();
        reserved[b] = any_u64();
        m->usable_expect[b] = usable[b];
        m->blocked_expect[b] = blocked[b];
        m->reserved_expect[b] = reserved[b];
    }
    for (uint32_t k = 0; k < 2; ++k) {
        for (uint32_t i = 0; i < WORDS; ++i) {
            states[k][i] = any_u64();
            m->states_expect[k][i] = states[k][i];
        }
    }
    uint32_t total_record = nondet_u32(), total_prior = total_record;
    uint32_t length_record = nondet_u32(), length_prior = length_record;
    uint32_t current_record = nondet_u32(), current_prior = current_record;
    struct boot_projection_storage projection;
    projection.record = projection_record;
    projection.context = m;
    projection.usable = usable;
    projection.blocked = blocked;
    projection.reserved = reserved;
    m->copy_expect = copy_expect;
    m->info_expect = m->call == CALL_ALLOCATE ? copy_expect : info_expect;
    m->extent_ok = 0;
    m->records = 0;
    m->at = 0;
    if (m->call == CALL_ALLOCATE) {
        if (m->magic != BOOT_HANDOFF_MULTIBOOT2_MAGIC) stop(m, BOOT_HANDOFF_MAGIC);
        else if ((m->address & 7) != 0) stop(m, BOOT_HANDOFF_POINTER_ALIGNMENT);
        else if (m->address < BOOT_HANDOFF_PAGE_BYTES) stop(m, BOOT_HANDOFF_POINTER_LOW);
        else if (m->address >= BOOT_HANDOFF_ACCESSIBLE_LIMIT) stop(m, BOOT_HANDOFF_POINTER_HIGH);
        else m->expect = EXPECT_SIZE;
    } else if (m->call == CALL_COPY) {
        begin_stream(m);
    } else {
        begin_decode(m);
    }

    m->running = 1;
    enum boot_handoff_status status;
    if (m->call == CALL_ALLOCATE) {
        status = handoff_extent(bootloader_read, m, m->magic, m->address, &total_record);
        if (status == BOOT_HANDOFF_OK)
            status = handoff_project(bootloader_read, m, m->magic, m->address, total_record, copy, &projection,
                                     states, &current_record);
    } else if (m->call == CALL_COPY) {
        status = handoff_copy(bootloader_read, m, m->magic, m->address, m->total, copy, &length_record);
    } else if (m->call == CALL_PROJECTION) {
        status = handoff_projection(m->magic, m->address, m->total, info, &projection, states, &current_record);
    } else {
        status = handoff_candidate(m->magic, m->address, m->total, m->candidate, info, states, &current_record);
    }

    qp_assert(m->expect == EXPECT_NOTHING);
    qp_assert(status == m->verdict);
    for (uint32_t i = 0; i < copy_words; ++i)
        qp_assert(copy[i] == copy_expect[i]);
    for (uint32_t i = 0; i < info_words; ++i)
        qp_assert(info[i] == info_expect[i]);
    for (uint32_t b = 0; b < BLOCKS; ++b)
        qp_assert(usable[b] == m->usable_expect[b] && blocked[b] == m->blocked_expect[b] &&
                  reserved[b] == m->reserved_expect[b]);
    for (uint32_t k = 0; k < 2; ++k)
        for (uint32_t i = 0; i < WORDS; ++i)
            qp_assert(states[k][i] == m->states_expect[k][i]);
    qp_assert(total_record == (m->extent_ok ? m->total : total_prior));
    qp_assert(length_record == (m->call == CALL_COPY && status == BOOT_HANDOFF_OK ? m->total : length_prior));
    qp_assert(current_record == (m->call != CALL_COPY && status == BOOT_HANDOFF_OK ? m->at : current_prior));
    return 0;
}
