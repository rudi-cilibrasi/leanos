/* Value distributions of the law handoff_decode_exact for native and interpreter runs (not part of any theorem).
 * The law draws the function, the magic, the address, the extent and the candidate (two u32), then the prior
 * values of every object (two u32 per word) and of the three records, and then, once main sets law.running, two
 * u32 per bootloader read and per answer of the adversarial Lean.  Uniform values would stop every run at the magic
 * or the first answer.  So this plan builds, per run, an information whose size word declares the planned extent
 * and answers what an accepting stream, decoder and projection would, reading the law's model
 * (harness/handoff_decode_exact.h) for the chunk, the state and the word it is at: the stream echoes its bound
 * identity, extent, offsets and chunks, the decoder accepts every transition, completes at the last one with phase
 * 7 and its target, and raises entry events at planned chunks with counts that rise from 1, and every block
 * projection accepts.  Words no check reads are random; in half the runs every decoder word no check reads is,
 * so that each carried word differs from the others.  Each run then
 * perturbs at most one place, with values next to each check's boundary: the magic, the address, the size word,
 * one reset or transition word of the stream or the decoder, an event's count, one block projection, the final
 * state, or a rejection by the decoder; and one run in eight answers one call with any value.  A few runs carry
 * 64 KiB natively; under the interpreter (GP_RUNS
 * defined), whose budget per seed they exceed, at most 6 chunks and 1 event, and half the runs decode alone
 * (the 8192 words of an allocation's or a copy's copy take it about 5 s to fill and compare). */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"
#include "../harness/handoff_decode_exact.h"

extern uint64_t quickproof_rnd(void);

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

enum { ENV_NONE, ENV_MAGIC, ENV_POINTER, ENV_BOUNDS, ENV_STREAM_INIT, ENV_STREAM_STEP, ENV_DECODE_INIT,
       ENV_DECODE_STEP, ENV_COUNT, ENV_ENTRY, ENV_FINAL, ENV_REJECT, ENV_TARGETS };
#define ENV_EVENTS 64u

static int env_planned, env_target, env_pick, env_have_lo;
static unsigned long env_inputs;
static uint64_t env_pending_lo;
static uint32_t env_call, env_magic, env_address, env_total, env_chunks;
static uint64_t env_candidate;
static uint32_t env_size_low;      /* the size word's low half as the bootloader answers it */
static long env_at_chunk;          /* the chunk of the perturbed transition */
static int env_at_word;            /* its word */
static long env_at_event, env_at_block;
static int env_value_kind;
static long env_random_at, env_answers;   /* one answer, of any value, at answer env_random_at */
static int env_wild;                      /* the decoder answers words no check reads with any values */
static uint64_t env_event_count;   /* events raised so far */
static long env_events_planned;
static uint64_t env_event_mask[(8192 + 63) / 64];

static int env_is_event(uint64_t k) { return (int)((env_event_mask[k / 64] >> (k % 64)) & 1u); }

static void env_plan(void) {
    env_planned = 1;
    /* 40% allocations, 15% copies, 20% projections and 25% candidates alone. */
    static const int calls[20] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3};
    env_call = (uint32_t)calls[env_r(20)];
#ifdef GP_RUNS
    /* The interpreter fills and compares an allocation's or a copy's 8192 words in about 5 s: half the seeds. */
    static const int interp_calls[10] = {0, 0, 0, 0, 1, 2, 2, 2, 3, 3};
    env_call = (uint32_t)interp_calls[env_r(10)];
#endif
    /* The perturbations that apply to each function, each about as likely as the others. */
    static const int allocate_targets[16] = {ENV_NONE, ENV_NONE, ENV_MAGIC, ENV_POINTER, ENV_POINTER, ENV_BOUNDS,
                                             ENV_BOUNDS, ENV_STREAM_INIT, ENV_STREAM_STEP, ENV_STREAM_STEP,
                                             ENV_DECODE_INIT, ENV_DECODE_STEP, ENV_COUNT, ENV_ENTRY, ENV_FINAL,
                                             ENV_REJECT};
    static const int copy_targets[4] = {ENV_NONE, ENV_STREAM_INIT, ENV_STREAM_STEP, ENV_STREAM_STEP};
    static const int projection_targets[8] = {ENV_NONE, ENV_DECODE_INIT, ENV_DECODE_STEP, ENV_COUNT, ENV_ENTRY,
                                              ENV_FINAL, ENV_REJECT, ENV_REJECT};
    static const int candidate_targets[8] = {ENV_NONE, ENV_DECODE_INIT, ENV_DECODE_INIT, ENV_DECODE_STEP,
                                             ENV_DECODE_STEP, ENV_FINAL, ENV_REJECT, ENV_REJECT};
    env_target = env_call == CALL_ALLOCATE ? allocate_targets[env_r(16)] :
                 env_call == CALL_COPY ? copy_targets[env_r(4)] :
                 env_call == CALL_PROJECTION ? projection_targets[env_r(8)] : candidate_targets[env_r(8)];
    env_pick = (int)env_r(16);
    env_value_kind = (int)env_r(8);
    env_wild = (int)env_r(2);
    env_magic = BOOT_HANDOFF_MULTIBOOT2_MAGIC;
    env_address = 0x1000u + 8u * (uint32_t)env_r(0x1000000u / 8u - 0x2000u - 8192u);
    /* Mostly 2 to 64 chunks; sometimes none or one (a copy or a decoding alone), or many. */
    unsigned k = (unsigned)env_r(40);
    env_chunks = k < 30 ? 2 + (uint32_t)env_r(63) : k < 34 ? (uint32_t)env_r(2) : k < 38 ? 65 + (uint32_t)env_r(400) :
                 8192 - (uint32_t)env_r(2);
#ifdef GP_RUNS
    /* The interpreter runs each transition's 41 calls and checks too slowly for many chunks. */
    env_chunks = env_chunks % 7;
#endif
    if (env_call == CALL_ALLOCATE && env_chunks < 2) env_chunks = 2;
    env_total = 8 * env_chunks;
    /* An allocation's information: mostly anywhere, sometimes at the lowest accepted address or ending exactly at
       the accessible limit. */
    unsigned place = (unsigned)env_r(8);
    if (place == 0) env_address = 0x1000u;
    else if (place == 1) env_address = 0x1000000u - env_total;
    env_candidate = env_r(4) == 0 ? quickproof_rnd() : env_r(4096);
    if (env_call != CALL_ALLOCATE && env_r(4) == 0) {   /* a copy or a decoding alone checks neither */
        env_magic = (uint32_t)quickproof_rnd();
        env_address = (uint32_t)quickproof_rnd();
    }
    env_size_low = env_total;
    /* Entry events: on a quarter of the chunks, at most ENV_EVENTS (2 under the interpreter). */
    long cap = (long)ENV_EVENTS;
#ifdef GP_RUNS
    cap = 1;
#endif
    if (env_chunks > 2000) cap = 4;
    env_events_planned = 0;
    for (uint32_t c = 0; c < env_chunks && env_events_planned < cap; ++c) {
        if (env_r(4) == 0) {
            env_event_mask[c / 64] |= (uint64_t)1 << (c % 64);
            ++env_events_planned;
        }
    }
    env_at_chunk = env_chunks ? (env_r(2) ? (long)env_chunks - 1 : (long)env_r(env_chunks)) : 0;
    /* A rejection before the last chunk, where the decoder must stop, as often as one at the last. */
    if (env_target == ENV_REJECT && env_chunks > 1 && env_r(2)) env_at_chunk = (long)env_r(env_chunks - 1);
    env_random_at = env_r(8) == 0 ? (long)env_r(env_r(2) ? 64 : 4000) : -1;
    env_at_word = 0;
    env_at_event = env_events_planned ? (long)env_r((uint64_t)env_events_planned) : -1;
    env_at_block = env_r(2) ? 63 : (long)env_r(64);
    switch (env_target) {
    case ENV_MAGIC: {
        static const uint32_t bad[4] = {0, 0x36d76288u, 0x36d7628au, 0xb6d76289u};
        env_magic = bad[env_pick % 4];
        if (env_call != CALL_ALLOCATE && env_pick % 2) env_magic = (uint32_t)quickproof_rnd();
        break;
    }
    case ENV_POINTER: {
        /* Unaligned, below the first page, the lowest and the highest accepted addresses, the limit and beyond. */
        static const uint32_t addresses[8] = {0x1004u, 0u, 8u, 0xff8u, 0x1000u, 0xfffff8u, 0x1000000u, 0xfffffff8u};
        env_address = addresses[env_pick % 8];
        if (env_pick % 8 == 0) env_address = 0x1000u + 8u * (uint32_t)env_r(1000) + 1u + (uint32_t)env_r(7);
        break;
    }
    case ENV_BOUNDS: {
        /* Below 16, the smallest extent, above 64 KiB, unaligned. */
        static const uint32_t sizes[8] = {0, 8, 15, 16, 65537, 65544, 0xffffffffu, 17};
        if (env_pick < 8) {
            env_size_low = sizes[env_pick];
            if (env_pick == 3) {
                env_total = 16;
                env_chunks = 2;
            }
            if (env_pick == 7) env_size_low = 16 + 8 * (uint32_t)env_r(100) + 1 + (uint32_t)env_r(7);
        } else if (env_pick < 12) {
            /* The information ends at (12, 13: within, past) or crosses (14, 15) the accessible limit. */
            env_address = 0x1000000u - 8u * (uint32_t)(2 + env_r(16));
            uint32_t room = 0x1000000u - env_address;
            env_size_low = env_pick % 2 ? room + 8 : room;
            env_chunks = env_size_low / 8;
            env_total = env_size_low;
        } else {
            env_size_low = 65536;   /* the largest accepted extent */
#ifdef GP_RUNS
            env_size_low = 16 + 8 * (uint32_t)env_r(5);
#endif
            env_total = env_size_low;
            env_chunks = env_total / 8;
            for (uint32_t c = 0; c < (8192 + 63) / 64; ++c) env_event_mask[c] = 0;
            env_events_planned = 0;
            env_target = ENV_NONE;
        }
        break;
    }
    case ENV_STREAM_INIT:
        env_at_word = (int)env_r(7);
        break;
    case ENV_STREAM_STEP:
        env_at_word = (int)env_r(9);
        break;
    case ENV_DECODE_INIT: {   /* mostly the words the reset's checks read */
        static const int words[12] = {0, 1, 2, 3, 4, 5, 16, 18, 30, 0, 2, 7};
        env_at_word = env_r(12) ? words[env_r(12)] : (int)env_r(41);
        break;
    }
    case ENV_DECODE_STEP: {
        static const int words[12] = {0, 1, 1, 2, 5, 7, 11, 16, 19, 19, 20, 40};
        env_at_word = env_r(12) ? words[env_r(12)] : (int)env_r(41);
        break;
    }
    case ENV_FINAL: {
        static const int words[5] = {1, 2, 5, 7, 16};
        env_at_word = words[env_r(5)];
        env_at_chunk = (long)env_chunks - 1;
        break;
    }
    case ENV_ENTRY:
        env_at_word = (int)env_r(4);
        break;
    default:
        break;
    }
}

/* The accepting answer to the call the law is at, before any perturbation. */
static uint64_t env_accepting(void) {
    struct law *m = &law;
    uint64_t w = m->word;
    switch (m->expect) {
    case EXPECT_SIZE:
        return quickproof_rnd() << 32 | env_size_low;
    case EXPECT_CHUNK:
        if (m->chunk == 0 && env_r(2)) return quickproof_rnd() << 32 | m->total;
        return env_r(4) ? quickproof_rnd() : env_r(4);
    case EXPECT_STREAM_INIT: {
        const uint64_t v[7] = {2, 0, 0, m->address, m->total, 0, quickproof_rnd()};
        return v[w < 7 ? w : 6];
    }
    case EXPECT_STREAM_STEP: {
        uint64_t last = 8 * m->chunk + 8 == m->total;
        const uint64_t v[9] = {2, last, 0, m->address, m->total, 8 * m->chunk + 8, quickproof_rnd(), m->value, 8};
        return v[w < 9 ? w : 6];
    }
    case EXPECT_DECODE_INIT:
        if (w == 0) return 5;
        if (w == 1 || w == 2 || w == 5 || w == 18 || w == 30) return 0;
        if (w == 3) return m->address;
        if (w == 4) return m->total;
        if (w == 16) return m->candidate;
        if (w == 19) return env_r(2);
        return env_r(3) ? quickproof_rnd() : env_r(8);
    case EXPECT_DECODE_STEP: {
        /* Only word 2, word 19 with a projection and the final checks' words are read; in a wild run every other
           word is any value, so each word the next transition carries differs from the others. */
        uint64_t last = 8 * m->chunk + 8 == m->total;
        int event = m->projection && env_is_event(m->chunk);
        int wild = env_wild && !last;
        if (w == 2) return 0;
        if (w == 19 && m->projection) return event ? 1 : env_wild ? quickproof_rnd() | 2 : env_r(3) * 2;
        if (w == 11 && event)   /* the count rises from 1, or in a wild run is any slot, the bounds' often */
            return env_wild ? (uint64_t[]){1, 256, 255, 1 + env_r(256)}[env_r(4)] : env_event_count + 1;
        if (wild || (env_wild && (w == 0 || w == 3 || w == 4 || w == 11 || (w == 16 && m->projection))))
            return env_r(4) ? quickproof_rnd() : env_r(8);
        if (w == 0) return 5;
        if (w == 1) return last;
        if (w == 3) return m->address;
        if (w == 4) return m->total;
        if (w == 5) return 8 * m->chunk + 8;
        if (w == 7) return last ? 7 : env_r(7);
        if (w == 11) return env_r(300);
        if (w == 16) return m->candidate;
        if (w == 19) return env_r(2);
        return env_r(3) ? quickproof_rnd() : env_r(8);
    }
    case EXPECT_ENTRY:
        if (w == 0) return 1;
        if (w == 1) return 0;
        return quickproof_rnd();
    default:
        return quickproof_rnd();
    }
}

/* A value next to the boundary of the check of word `word` whose accepted value is `v`. */
static uint64_t env_near(uint64_t v) {
    switch (env_value_kind) {
    case 0: return v + 1;
    case 1: return v - 1;
    case 2: return v ^ ((uint64_t)1 << 32);
    case 3: return v ^ ((uint64_t)1 << 63);
    case 4: return 0;
    case 5: return v + 8;
    case 6: return 0xffffffffffffffffu;
    default: return v ^ (1 + env_r(255));
    }
}

/* The answer to the call the law is at. */
static uint64_t env_answer(void) {
    struct law *m = &law;
    uint64_t v = env_accepting();
    long w = (long)m->word;
    switch (env_target) {
    case ENV_STREAM_INIT:
        if (m->expect == EXPECT_STREAM_INIT && w == env_at_word) v = env_near(v);
        break;
    case ENV_STREAM_STEP:
        if (m->expect == EXPECT_STREAM_STEP && (long)m->chunk == env_at_chunk && w == env_at_word) v = env_near(v);
        break;
    case ENV_DECODE_INIT:
        if (m->expect == EXPECT_DECODE_INIT && w == env_at_word) v = env_near(v);
        break;
    case ENV_DECODE_STEP:
        if (m->expect == EXPECT_DECODE_STEP && (long)m->chunk == env_at_chunk && w == env_at_word) {
            if (w == 19) v = v == 1 ? 0 : 1;
            else v = env_near(v);
        }
        break;
    case ENV_FINAL:
        if (m->expect == EXPECT_DECODE_STEP && (long)m->chunk == env_at_chunk && w == env_at_word) v = env_near(v);
        break;
    case ENV_REJECT:
        /* The decoder rejects one chunk: a typed error, with the rejected status or (adversarially) another. */
        if (m->expect == EXPECT_DECODE_STEP && (long)m->chunk == env_at_chunk) {
            if (w == 2) v = 1 + env_r(13);
            else if (w == 1) v = (uint64_t[]){2, 2, 0, 1}[env_pick % 4];
            else if (w != 0 && env_pick % 2) v = 0;
        }
        break;
    case ENV_COUNT:
        if (m->expect == EXPECT_DECODE_STEP && w == 11 && m->projection && env_is_event(m->chunk) &&
            (long)env_event_count == env_at_event) {
            static const uint64_t counts[8] = {0, 257, 256, 1, 0x100000000u, 0xffffffffffffffffu, 255, 258};
            v = counts[env_value_kind];
        }
        break;
    case ENV_ENTRY:
        if (m->expect == EXPECT_ENTRY && (long)env_event_count - 1 == env_at_event && (long)m->block == env_at_block &&
            w == env_at_word)
            v = w < 2 ? env_near(v) : v;
        break;
    default:
        break;
    }
    if (m->expect == EXPECT_DECODE_STEP && w == WORDS - 1 && m->projection && env_is_event(m->chunk))
        ++env_event_count;
    return v;
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    if (!law.running) {
        unsigned long k = env_inputs++;
        if (k < 6) {   /* the function, the magic, the address, the extent, the candidate (high word first) */
            const uint64_t v[6] = {env_call, env_magic, env_address, env_total, env_candidate >> 32,
                                   env_candidate & 0xffffffffu};
            return (uint32_t)v[k];
        }
        return (uint32_t)quickproof_rnd();
    }
    if (env_have_lo) {
        env_have_lo = 0;
        return (uint32_t)env_pending_lo;
    }
    uint64_t v = env_answer();
    if (env_answers++ == env_random_at) v = env_r(2) ? quickproof_rnd() : env_r(4);
    env_pending_lo = v & 0xffffffffu;
    env_have_lo = 1;
    return (uint32_t)(v >> 32);
}

uint8_t nondet_u8(void) { return (uint8_t)quickproof_rnd(); }

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
