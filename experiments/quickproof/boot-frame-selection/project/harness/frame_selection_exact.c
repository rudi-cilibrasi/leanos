/* Law frame_selection_exact.  The candidate decoder, the scrub and the six Lean exports the header calls are this
   harness's: a decoder that writes any 41 words to the state it is given and answers any status, a scrub that answers
   any value, and an adversarial Lean that answers every call with any 64-bit value, all different on every call; each
   of them checks every call.  For every manifest of 18 words, every decoded state of the projection's decoder (41
   words), usable, blocked and reserved bitmaps of 64 words, a terminal result of 9 words, two decoder states of 41
   words (state 0 and state 1), a publication result and a rescan record of 5 words and four records (the selected
   frame, its manifest answer, the next frame and the decoder's status), every object holding any values, for every
   take_next and every frame argument of a step alone (any 64-bit values), main calls boot_allocate's sequence of the
   steps of include/boot_frame_selection.h (patch/frame_unit.c), or one step alone, and each step behaves as follows.
   Statuses are those of the header without the prefix BOOT_FRAME_; word q of a result is the answer to its call for
   query q; every call that takes the manifest gets its 18 words, in order.
     - Terminal (boot_frame_terminal): for each block b of 0..63 in order it calls the manifest overlay 3 times, for
       words 1, 2 and 3 in order, each with b and the manifest, writes word 3 to word b of the reserved bitmap, then
       calls the free word once with words b of the usable and blocked bitmaps and that word 3.  The overlay's status
       and error are 1 and 0, unless a block answered word 1 other than 1 or word 2 other than 0: then words 1 and 2
       of the last such block.  Then it calls the terminal result 9 times, for words 0..8 in order, each with words 1
       and 2 of the decoded state, the overlay's status and error, words 11 and 17 of the decoded state, owner 1 and
       the 64 free words in block order, and writes word q to word q of the terminal result.  It returns
       TERMINAL_VERSION, _STATUS, _ERROR, _FRAME, _OWNER or _ENTRY_COUNT, the first that applies, unless words 0..5
       are 1, 1, 0, below 4096, 1 and word 11 of the decoded state; else OK.
     - Selection (boot_frame_select): for each candidate c = 0, 1, ... below 4096 in order it calls the decoder once
       with c and state 0 until a candidate is accepted, state 1 after; at a decoder status other than 0 it returns
       DECODER at once, writing the status to the decoder record.  Otherwise it calls the manifest's answer once with
       c and the manifest, then the consumer once with 4096, c, words 1, 14 and 15 of the state just decoded and the
       manifest's answer.  A consumer answer below 4096 accepts c: the first is the selected frame, with c's manifest
       answer; with take_next 0 the scan stops there, otherwise it goes on and the second answer below 4096 is the
       next frame, where it stops.  It stops after candidate 4095 too.  Then it returns OK, writing the selected
       frame, its manifest answer and the next frame to their records (4096, 0 and 4096 for a frame not found).
     - Cross-check (boot_frame_cross_check, with a frame S and a manifest answer A, and state 0 as the selected
       candidate's): without a call, it returns AUTHORITY_NONE, _NOMINATION, _TARGET, _ENTRY_COUNT, _HIGHEST, _USABLE,
       _BLOCKED or _MANIFEST, the first that applies, unless S is below 4096 and is word 3 of the terminal result and
       word 16 of state 0, words 11 and 17 of state 0 are those of the decoded state, its words 14 and 15 are 1 and 0,
       and A is 1; else OK.
     - Scrub (boot_frame_scrub_selected, with a frame S): it calls the scrub once with S, and returns OK when the
       scrub answered 1, SCRUB otherwise.
     - Publication (boot_frame_publication_result, then boot_frame_publication_check, with S and A as above): it calls
       the authority result 5 times, for words 0..4 in order, each with S, words 16, 1, 14 and 15 of state 0, A and a
       scrubbed frame (1), and writes word q to word q of the publication result.  Then, without a call, the check
       returns PUBLICATION_VERSION, _STATUS, _ERROR, _FRAME or _OBJECT, the first that applies, unless the words are 1,
       1, 0, S and S + 1; else OK.
     - Rescan (boot_frame_rescan, with a published frame P and a next frame N): without a call, it returns
       UNPUBLISHED_LIMIT unless N is below 4096, then UNPUBLISHED_ORDER unless N is above P.  Otherwise it calls the
       decoder once with N and state 1 (DECODER at a status other than 0, as above), then the manifest's answer once
       with N and the manifest, and returns RESCAN_ENTRY_COUNT, _HIGHEST, _TARGET, _STATUS, _USABLE, _BLOCKED or
       _MANIFEST, the first that applies, unless words 11 and 17 of state 1 are those of the decoded state, its word
       16 is N, its words 1, 14 and 15 are 1, 1 and 0, and the manifest's answer is 1; else OK, writing words 16, 1, 14
       and 15 of state 1 and the manifest's answer to the rescan record.
     - boot_allocate's sequence: the terminal, the selection, the cross-check, the scrub, the publication and, with
       take_next nonzero, the rescan, each only once every step before it returned OK.  As boot_allocate passes them,
       the cross-check, the scrub and the publication take the selected frame and its manifest answer from the
       selection's records, and the rescan the selected frame as P and the next frame as N.  So the decoder is called
       for exactly the candidates 0, 1, ... up to the first accepted (the second with take_next, and then the next
       frame once more), the scrub only once every check accepted, once, with exactly the selected frame, and the
       authority result only after the scrub answered 1.
     - Calls and writes: no step makes a call but those above, in that order, and none after the check that decides
       its status.  The decoder writes only the state it is given.  The terminal writes only the reserved bitmap and
       the terminal result; the selection only its three records on OK, and the decoder record on DECODER; the
       publication result only its five words; the rescan only its record on OK, and the decoder record on DECODER;
       the cross-check, the scrub and the check write nothing.  Every other word of every object keeps its value.
   So no Lean answer, decoder or scrub can make the header skip a block or a candidate, ask about another block,
   candidate, state, frame or manifest than the ones it carries, select a frame other than the first the consumer
   accepts, take a decoder's rejected candidate, scrub a frame before every cross-check accepts it or another frame
   than the selected one, ask the publication before the scrub succeeded, write outside its results, or return OK
   when an answer it checks rejects.  The decoder, the scrub and the Lean exports below are the reference: they keep
   the state the header must carry and check every call against it, and the law's model
   (harness/frame_selection_exact.h) keeps its own copy of what memory must hold; after each step main compares the
   status, every object and the records.  Not claimed: termination (partial correctness; every loop is bounded); what
   the Lean answers mean (the BootMemoryMapStreamAuthority theorems); that the kernel's decoder is
   boot_handoff_decode_candidate over the handoff copy, which experiments/quickproof/boot-handoff-decode proves, and
   what the kernel's scrub does to physical memory; the kernel's mapping from statuses to reasons and its mutation
   fixtures between the steps (scripts/check-boot-handoff-stream.sh checks both on the source). */
#include <stdlib.h>
#include "quickproof.h"
#include "frame_selection_exact.h"

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

/* The manifest a call got is the manifest. */
static int same_manifest(const uint64_t *words) {
    for (uint32_t i = 0; i < MANIFEST; ++i)
        if (words[i] != law.manifest[i]) return 0;
    return 1;
}

/* The selection's scan ended: its result. */
static void select_done(struct law *m) {
    m->selected_expect = m->first;
    m->manifest_expect = m->first_manifest;
    m->next_expect = m->second;
    stop(m, BOOT_FRAME_OK);
}

/* The candidate after the current one, or the end of the scan. */
static void next_candidate(struct law *m) {
    if (m->candidate + 1 < FRAMES) {
        m->candidate = m->candidate + 1;
        m->expect = EXPECT_DECODE;
    } else {
        select_done(m);
    }
}

/* The candidate decoder: any 41 words into the state it is given, then any status. */
static uint32_t law_decode(void *context, uint64_t candidate, uint64_t *state) {
    struct law *m = &law;
    qp_assert(context == (void *)m && m->expect == EXPECT_DECODE && candidate == m->candidate);
    qp_assert(state == m->states[m->scan]);
    for (uint32_t i = 0; i < WORDS; ++i) {
        m->word = i;
        uint64_t v = any_u64();
        state[i] = v;
        m->states_expect[m->scan][i] = v;
    }
    m->word = WORDS;
    uint32_t status = (uint32_t)any_u64();
    if (status != 0) {
        m->decoder_expect = status;
        stop(m, BOOT_FRAME_DECODER);
    } else {
        m->expect = EXPECT_CANDIDATE;
    }
    return status;
}

/* The scrub: any answer. */
static uint32_t law_scrub(void *context, uint64_t frame) {
    struct law *m = &law;
    qp_assert(context == (void *)m && m->expect == EXPECT_SCRUB && frame == m->selected);
    uint32_t v = (uint32_t)any_u64();
    m->scrubbed = v == 1;
    stop(m, v == 1 ? BOOT_FRAME_OK : BOOT_FRAME_SCRUB);
    return v;
}

uint64_t leanos_boot_projection_manifest(uint64_t block, uint64_t m0, uint64_t m1, uint64_t m2, uint64_t m3,
                                         uint64_t m4, uint64_t m5, uint64_t m6, uint64_t m7, uint64_t m8, uint64_t m9,
                                         uint64_t m10, uint64_t m11, uint64_t m12, uint64_t m13, uint64_t m14,
                                         uint64_t m15, uint64_t m16, uint64_t m17, uint64_t query) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_MANIFEST && block == m->block && query == m->word);
    const uint64_t words[MANIFEST] = {m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17};
    qp_assert(same_manifest(words));
    uint64_t v = any_u64();
    m->answer[m->word] = v;
    if (m->word < 3) {
        m->word = m->word + 1;
        return v;
    }
    if (m->answer[1] != 1 || m->answer[2] != 0) {
        m->manifest_status = m->answer[1];
        m->manifest_error = m->answer[2];
    }
    m->reserved_expect[m->block] = m->answer[3];
    m->expect = EXPECT_FREE;
    return v;
}

uint64_t leanos_boot_projection_free(uint64_t usable, uint64_t blocked, uint64_t reserved) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_FREE);
    qp_assert(usable == m->usable[m->block] && blocked == m->blocked[m->block] &&
              reserved == m->reserved_expect[m->block]);
    uint64_t v = any_u64();
    m->free_words[m->block] = v;
    if (m->block + 1 < BLOCKS) {
        m->block = m->block + 1;
        m->word = 1;
        m->expect = EXPECT_MANIFEST;
    } else {
        m->word = 0;
        m->expect = EXPECT_FINISH;
    }
    return v;
}

uint64_t leanos_boot_projection_finish(
        uint64_t decode_status, uint64_t decode_error, uint64_t manifest_status, uint64_t manifest_error,
        uint64_t entry_count, uint64_t highest, uint64_t owner, uint64_t query,
        uint64_t w00, uint64_t w01, uint64_t w02, uint64_t w03, uint64_t w04, uint64_t w05, uint64_t w06,
        uint64_t w07, uint64_t w08, uint64_t w09, uint64_t w10, uint64_t w11, uint64_t w12, uint64_t w13,
        uint64_t w14, uint64_t w15, uint64_t w16, uint64_t w17, uint64_t w18, uint64_t w19, uint64_t w20,
        uint64_t w21, uint64_t w22, uint64_t w23, uint64_t w24, uint64_t w25, uint64_t w26, uint64_t w27,
        uint64_t w28, uint64_t w29, uint64_t w30, uint64_t w31, uint64_t w32, uint64_t w33, uint64_t w34,
        uint64_t w35, uint64_t w36, uint64_t w37, uint64_t w38, uint64_t w39, uint64_t w40, uint64_t w41,
        uint64_t w42, uint64_t w43, uint64_t w44, uint64_t w45, uint64_t w46, uint64_t w47, uint64_t w48,
        uint64_t w49, uint64_t w50, uint64_t w51, uint64_t w52, uint64_t w53, uint64_t w54, uint64_t w55,
        uint64_t w56, uint64_t w57, uint64_t w58, uint64_t w59, uint64_t w60, uint64_t w61, uint64_t w62,
        uint64_t w63) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_FINISH && query == m->word);
    qp_assert(decode_status == m->decoded[1] && decode_error == m->decoded[2] &&
              manifest_status == m->manifest_status && manifest_error == m->manifest_error &&
              entry_count == m->decoded[11] && highest == m->decoded[17] && owner == 1);
    const uint64_t words[BLOCKS] = {
        w00, w01, w02, w03, w04, w05, w06, w07, w08, w09, w10, w11, w12, w13, w14, w15,
        w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31,
        w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47,
        w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63};
    for (uint32_t b = 0; b < BLOCKS; ++b)
        qp_assert(words[b] == m->free_words[b]);
    uint64_t v = any_u64();
    m->terminal_expect[m->word] = v;
    if (m->word < TERMINAL - 1) {
        m->word = m->word + 1;
        return v;
    }
    const uint64_t *t = m->terminal_expect;
    if (t[0] != 1) stop(m, BOOT_FRAME_TERMINAL_VERSION);
    else if (t[1] != 1) stop(m, BOOT_FRAME_TERMINAL_STATUS);
    else if (t[2] != 0) stop(m, BOOT_FRAME_TERMINAL_ERROR);
    else if (t[3] >= FRAMES) stop(m, BOOT_FRAME_TERMINAL_FRAME);
    else if (t[4] != 1) stop(m, BOOT_FRAME_TERMINAL_OWNER);
    else if (t[5] != m->decoded[11]) stop(m, BOOT_FRAME_TERMINAL_ENTRY_COUNT);
    else stop(m, BOOT_FRAME_OK);
    return v;
}

uint64_t leanos_boot_manifest_candidate(uint64_t frame, uint64_t m0, uint64_t m1, uint64_t m2, uint64_t m3,
                                        uint64_t m4, uint64_t m5, uint64_t m6, uint64_t m7, uint64_t m8, uint64_t m9,
                                        uint64_t m10, uint64_t m11, uint64_t m12, uint64_t m13, uint64_t m14,
                                        uint64_t m15, uint64_t m16, uint64_t m17) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_CANDIDATE && frame == m->candidate);
    const uint64_t words[MANIFEST] = {m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17};
    qp_assert(same_manifest(words));
    uint64_t v = any_u64();
    m->candidate_manifest = v;
    if (m->step == STEP_SELECT) {
        m->expect = EXPECT_CONSUME;
        return v;
    }
    /* The rescan of the next frame, decoded into state 1. */
    const uint64_t *s = m->states_expect[m->scan];
    if (s[11] != m->decoded[11]) stop(m, BOOT_FRAME_RESCAN_ENTRY_COUNT);
    else if (s[17] != m->decoded[17]) stop(m, BOOT_FRAME_RESCAN_HIGHEST);
    else if (s[16] != m->candidate) stop(m, BOOT_FRAME_RESCAN_TARGET);
    else if (s[1] != 1) stop(m, BOOT_FRAME_RESCAN_STATUS);
    else if (s[14] != 1) stop(m, BOOT_FRAME_RESCAN_USABLE);
    else if (s[15] != 0) stop(m, BOOT_FRAME_RESCAN_BLOCKED);
    else if (v != 1) stop(m, BOOT_FRAME_RESCAN_MANIFEST);
    else {
        m->rescan_expect[0] = s[16];
        m->rescan_expect[1] = s[1];
        m->rescan_expect[2] = s[14];
        m->rescan_expect[3] = s[15];
        m->rescan_expect[4] = v;
        stop(m, BOOT_FRAME_OK);
    }
    return v;
}

uint64_t leanos_boot_consume_exact_projection(uint64_t current, uint64_t candidate, uint64_t decode_status,
                                              uint64_t usable, uint64_t blocked, uint64_t manifest) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_CONSUME);
    const uint64_t *s = m->states_expect[m->scan];
    qp_assert(current == FRAMES && candidate == m->candidate && decode_status == s[1] && usable == s[14] &&
              blocked == s[15] && manifest == m->candidate_manifest);
    uint64_t v = any_u64();
    if (v >= FRAMES) {
        next_candidate(m);
    } else if (m->scan == 0) {
        m->first = v;
        m->first_manifest = m->candidate_manifest;
        if (m->take_next == 0) {
            select_done(m);
        } else {
            m->scan = 1;
            next_candidate(m);
        }
    } else {
        m->second = v;
        select_done(m);
    }
    return v;
}

uint64_t leanos_boot_authority_result(uint64_t selected, uint64_t rescanned, uint64_t status, uint64_t usable,
                                      uint64_t blocked, uint64_t manifest, uint64_t scrubbed, uint64_t query) {
    struct law *m = &law;
    qp_assert(m->expect == EXPECT_AUTHORITY && query == m->word);
    const uint64_t *s = m->states_expect[0];
    qp_assert(selected == m->selected && rescanned == s[16] && status == s[1] && usable == s[14] &&
              blocked == s[15] && manifest == m->selected_manifest && scrubbed == 1);
    /* In boot_allocate's sequence, only once the scrub reported the frame zeroed. */
    qp_assert(m->call != CALL_ALLOCATE || m->scrubbed == 1);
    uint64_t v = any_u64();
    m->publication_expect[m->word] = v;
    if (m->word < PUBLICATION - 1)
        m->word = m->word + 1;
    else
        stop(m, BOOT_FRAME_OK);
    return v;
}

/* The steps' turns: the expected first call, or the verdict of a step that makes none. */
static void begin_terminal(struct law *m) {
    m->step = STEP_TERMINAL;
    m->manifest_status = 1;
    m->manifest_error = 0;
    m->block = 0;
    m->word = 1;
    m->expect = EXPECT_MANIFEST;
}

static void begin_select(struct law *m) {
    m->step = STEP_SELECT;
    m->first = FRAMES;
    m->first_manifest = 0;
    m->second = FRAMES;
    m->scan = 0;
    m->candidate = 0;
    m->expect = EXPECT_DECODE;
}

static void begin_cross_check(struct law *m) {
    m->step = STEP_CROSS_CHECK;
    const uint64_t *s = m->states_expect[0];
    if (m->selected >= FRAMES) stop(m, BOOT_FRAME_AUTHORITY_NONE);
    else if (m->terminal_expect[3] != m->selected) stop(m, BOOT_FRAME_AUTHORITY_NOMINATION);
    else if (s[16] != m->selected) stop(m, BOOT_FRAME_AUTHORITY_TARGET);
    else if (s[11] != m->decoded[11]) stop(m, BOOT_FRAME_AUTHORITY_ENTRY_COUNT);
    else if (s[17] != m->decoded[17]) stop(m, BOOT_FRAME_AUTHORITY_HIGHEST);
    else if (s[14] != 1) stop(m, BOOT_FRAME_AUTHORITY_USABLE);
    else if (s[15] != 0) stop(m, BOOT_FRAME_AUTHORITY_BLOCKED);
    else if (m->selected_manifest != 1) stop(m, BOOT_FRAME_AUTHORITY_MANIFEST);
    else stop(m, BOOT_FRAME_OK);
}

static void begin_scrub(struct law *m) {
    m->step = STEP_SCRUB;
    m->expect = EXPECT_SCRUB;
}

static void begin_publication_result(struct law *m) {
    m->step = STEP_PUBLICATION_RESULT;
    m->word = 0;
    m->expect = EXPECT_AUTHORITY;
}

static void begin_publication_check(struct law *m) {
    m->step = STEP_PUBLICATION_CHECK;
    const uint64_t *p = m->publication_expect;
    if (p[0] != 1) stop(m, BOOT_FRAME_PUBLICATION_VERSION);
    else if (p[1] != 1) stop(m, BOOT_FRAME_PUBLICATION_STATUS);
    else if (p[2] != 0) stop(m, BOOT_FRAME_PUBLICATION_ERROR);
    else if (p[3] != m->selected) stop(m, BOOT_FRAME_PUBLICATION_FRAME);
    else if (p[4] != m->selected + 1) stop(m, BOOT_FRAME_PUBLICATION_OBJECT);
    else stop(m, BOOT_FRAME_OK);
}

static void begin_rescan(struct law *m) {
    m->step = STEP_RESCAN;
    if (m->next >= FRAMES) {
        stop(m, BOOT_FRAME_UNPUBLISHED_LIMIT);
    } else if (m->next <= m->published) {
        stop(m, BOOT_FRAME_UNPUBLISHED_ORDER);
    } else {
        m->candidate = m->next;
        m->scan = 1;
        m->expect = EXPECT_DECODE;
    }
}

/* After a step: it made every call it had to, returned its verdict, and memory is the model's. */
static void check_step(const struct law *m, uint32_t status, const uint64_t *manifest, const uint64_t *decoded,
                       const uint64_t *usable, const uint64_t *blocked, const uint64_t *reserved,
                       const uint64_t *terminal, uint64_t (*states)[WORDS], const uint64_t *publication,
                       const uint64_t *rescan, const uint64_t *records, const uint32_t *decoder_record) {
    qp_assert(m->expect == EXPECT_NOTHING);
    qp_assert(status == m->verdict);
    for (uint32_t i = 0; i < MANIFEST; ++i)
        qp_assert(manifest[i] == m->manifest[i]);
    for (uint32_t i = 0; i < WORDS; ++i)
        qp_assert(decoded[i] == m->decoded[i]);
    for (uint32_t b = 0; b < BLOCKS; ++b)
        qp_assert(usable[b] == m->usable[b] && blocked[b] == m->blocked[b] && reserved[b] == m->reserved_expect[b]);
    for (uint32_t i = 0; i < TERMINAL; ++i)
        qp_assert(terminal[i] == m->terminal_expect[i]);
    for (uint32_t k = 0; k < 2; ++k)
        for (uint32_t i = 0; i < WORDS; ++i)
            qp_assert(states[k][i] == m->states_expect[k][i]);
    for (uint32_t i = 0; i < PUBLICATION; ++i)
        qp_assert(publication[i] == m->publication_expect[i]);
    for (uint32_t i = 0; i < RESCAN; ++i)
        qp_assert(rescan[i] == m->rescan_expect[i]);
    qp_assert(records[0] == m->selected_expect && records[1] == m->manifest_expect && records[2] == m->next_expect);
    qp_assert(*decoder_record == m->decoder_expect);
}

int main(void) {
    struct law *m = &law;
    m->call = (uint32_t)any_u64() % CALLS;
    m->take_next = (uint32_t)any_u64();
    m->selected = any_u64();
    m->selected_manifest = any_u64();
    m->published = any_u64();
    m->next = any_u64();
    /* The storage, each object holding any values: the manifest, the decoded state, the three bitmaps, the
       terminal result, the two decoder states, the publication result, the rescan record and the records. */
    uint64_t *manifest = malloc(MANIFEST * sizeof(uint64_t));
    uint64_t *decoded = malloc(WORDS * sizeof(uint64_t));
    uint64_t *usable = malloc(BLOCKS * sizeof(uint64_t));
    uint64_t *blocked = malloc(BLOCKS * sizeof(uint64_t));
    uint64_t *reserved = malloc(BLOCKS * sizeof(uint64_t));
    uint64_t *terminal = malloc(TERMINAL * sizeof(uint64_t));
    uint64_t (*states)[WORDS] = malloc(2 * WORDS * sizeof(uint64_t));
    uint64_t *publication = malloc(PUBLICATION * sizeof(uint64_t));
    uint64_t *rescan = malloc(RESCAN * sizeof(uint64_t));
    uint64_t *records = malloc(3 * sizeof(uint64_t));
    uint32_t *decoder_record = malloc(sizeof(uint32_t));
    if (manifest == NULL || decoded == NULL || usable == NULL || blocked == NULL || reserved == NULL ||
        terminal == NULL || states == NULL || publication == NULL || rescan == NULL || records == NULL ||
        decoder_record == NULL)
        return 0;
    for (uint32_t i = 0; i < MANIFEST; ++i) {
        manifest[i] = any_u64();
        m->manifest[i] = manifest[i];
    }
    for (uint32_t i = 0; i < WORDS; ++i) {
        decoded[i] = any_u64();
        m->decoded[i] = decoded[i];
    }
    for (uint32_t b = 0; b < BLOCKS; ++b) {
        usable[b] = any_u64();
        m->usable[b] = usable[b];
    }
    for (uint32_t b = 0; b < BLOCKS; ++b) {
        blocked[b] = any_u64();
        m->blocked[b] = blocked[b];
    }
    for (uint32_t b = 0; b < BLOCKS; ++b) {
        reserved[b] = any_u64();
        m->reserved_expect[b] = reserved[b];
    }
    for (uint32_t i = 0; i < TERMINAL; ++i) {
        terminal[i] = any_u64();
        m->terminal_expect[i] = terminal[i];
    }
    for (uint32_t k = 0; k < 2; ++k) {
        for (uint32_t i = 0; i < WORDS; ++i) {
            states[k][i] = any_u64();
            m->states_expect[k][i] = states[k][i];
        }
    }
    for (uint32_t i = 0; i < PUBLICATION; ++i) {
        publication[i] = any_u64();
        m->publication_expect[i] = publication[i];
    }
    for (uint32_t i = 0; i < RESCAN; ++i) {
        rescan[i] = any_u64();
        m->rescan_expect[i] = rescan[i];
    }
    records[0] = any_u64();
    records[1] = any_u64();
    records[2] = any_u64();
    m->selected_expect = records[0];
    m->manifest_expect = records[1];
    m->next_expect = records[2];
    *decoder_record = (uint32_t)any_u64();
    m->decoder_expect = *decoder_record;
    m->states = states;
    m->scrubbed = 0;

    m->running = 1;
    uint32_t sequence = m->call == CALL_ALLOCATE;
    uint32_t status = BOOT_FRAME_OK;
    if (sequence || m->call == CALL_TERMINAL) {
        begin_terminal(m);
        status = frame_terminal(manifest, decoded, usable, blocked, reserved, terminal);
        check_step(m, status, manifest, decoded, usable, blocked, reserved, terminal, states, publication, rescan,
                   records, decoder_record);
    }
    if ((sequence && status == BOOT_FRAME_OK) || m->call == CALL_SELECT) {
        begin_select(m);
        status = frame_select(law_decode, m, manifest, m->take_next, states, &records[0], &records[1], &records[2],
                              decoder_record);
        check_step(m, status, manifest, decoded, usable, blocked, reserved, terminal, states, publication, rescan,
                   records, decoder_record);
        if (sequence) {
            /* boot_allocate passes the selection's records on. */
            m->selected = records[0];
            m->selected_manifest = records[1];
            m->published = records[0];
            m->next = records[2];
        }
    }
    if ((sequence && status == BOOT_FRAME_OK) || m->call == CALL_CROSS_CHECK) {
        begin_cross_check(m);
        status = frame_cross_check(terminal, decoded, m->selected, states[0], m->selected_manifest);
        check_step(m, status, manifest, decoded, usable, blocked, reserved, terminal, states, publication, rescan,
                   records, decoder_record);
    }
    if ((sequence && status == BOOT_FRAME_OK) || m->call == CALL_SCRUB) {
        begin_scrub(m);
        status = frame_scrub_selected(law_scrub, m, m->selected);
        check_step(m, status, manifest, decoded, usable, blocked, reserved, terminal, states, publication, rescan,
                   records, decoder_record);
    }
    if ((sequence && status == BOOT_FRAME_OK) || m->call == CALL_PUBLICATION) {
        begin_publication_result(m);
        frame_publication_result(m->selected, states[0], m->selected_manifest, publication);
        check_step(m, BOOT_FRAME_OK, manifest, decoded, usable, blocked, reserved, terminal, states, publication,
                   rescan, records, decoder_record);
        begin_publication_check(m);
        status = frame_publication_check(m->selected, publication);
        check_step(m, status, manifest, decoded, usable, blocked, reserved, terminal, states, publication, rescan,
                   records, decoder_record);
    }
    if ((sequence && status == BOOT_FRAME_OK && m->take_next != 0) || m->call == CALL_RESCAN) {
        begin_rescan(m);
        status = frame_rescan(law_decode, m, manifest, decoded, m->published, m->next, states[1], rescan,
                              decoder_record);
        check_step(m, status, manifest, decoded, usable, blocked, reserved, terminal, states, publication, rescan,
                   records, decoder_record);
    }
    return 0;
}
