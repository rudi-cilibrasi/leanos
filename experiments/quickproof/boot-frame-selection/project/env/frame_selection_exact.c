/* Value distributions of the law frame_selection_exact for native and interpreter runs (not part of any theorem).
 * main draws its inputs first, in the order of harness/frame_selection_exact.h (DRAW_*, two u32 each), then, once
 * main sets law.running, two u32 per decoder word, decoder status, scrub answer and answer of the adversarial Lean.
 * Uniform values would stop every run at the terminal result or the first consumer answer.  So this plan builds, per
 * run, inputs and answers that an accepting allocation would see, reading the law's model for the call, the block,
 * the candidate and the word it is at: the overlay accepts every block, the terminal result nominates the planned
 * frame with the decoder's entry count, the decoder accepts every candidate with the decoder's entry count and
 * highest frame and the candidate as its target, the consumer accepts the planned candidate (and, with take_next, a
 * later one) and answers at least 4096 before, the scrub and the publication accept, and so does the rescan.  A step
 * alone gets inputs that pass its checks.  Words no check reads are random; in half the runs every decoded word no
 * check reads is.  Each run then perturbs at most one place, with values next to each check's boundary: some
 * blocks' overlay status or error, one word of the terminal result, a decoder's rejection, the consumer's frame, one
 * condition of the cross-check, the scrub, one word of the publication, the next frame, or one condition of the
 * rescan; and one run in eight answers one call with any value.  Natively the first accepted candidate is mostly
 * among the first 16, sometimes anywhere or none (a scan of all 4096 candidates); under the interpreter (GP_RUNS
 * defined), whose budget per seed a long scan exceeds, it is among the first 4. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"
#include "../harness/frame_selection_exact.h"

extern uint64_t quickproof_rnd(void);

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

enum { ENV_NONE, ENV_OVERLAY, ENV_TERMINAL, ENV_DECODER, ENV_CONSUME, ENV_AUTHORITY, ENV_SCRUB, ENV_PUBLICATION,
       ENV_UNPUBLISHED, ENV_RESCAN };

static int env_planned, env_have_lo, env_target, env_value_kind, env_wild, env_word;
static unsigned long env_inputs_drawn;
static uint64_t env_pending_lo;
static uint64_t env_input[DRAWS];
static uint32_t env_call, env_take_next;
static uint64_t env_count, env_highest;   /* words 11 and 17 of the decoded state */
static long env_accept, env_accept2;      /* the accepted candidates (-1: none) */
static uint64_t env_frame, env_frame2;    /* the consumer's answers at them */
static long env_reject;                   /* the candidate the decoder rejects (-1: none) */
static long env_blocks[3];                /* the blocks whose overlay status or error is not 1 and 0 */
static long env_random_at, env_answers;   /* one answer, of any value, at answer env_random_at */

static uint64_t env_any(void) { return env_r(3) ? quickproof_rnd() : env_r(8); }

/* A value next to the boundary of the check whose accepted value is `v`. */
static uint64_t env_near(uint64_t v) {
    switch (env_value_kind) {
    case 0: return v + 1;
    case 1: return v - 1;
    case 2: return v ^ ((uint64_t)1 << 32);
    case 3: return v ^ ((uint64_t)1 << 63);
    case 4: return 0;
    case 5: return v + 4096;
    case 6: return 0xffffffffffffffffu;
    default: return v ^ (1 + env_r(255));
    }
}

/* A consumer answer that rejects: at least 4096, often exactly. */
static uint64_t env_reject_frame(void) {
    static const uint64_t frames[6] = {4096, 4096, 4097, 0xffffffffffffffffu, 0x8000000000000000u, 0x10000};
    return env_r(4) ? frames[env_r(6)] : 4096 + quickproof_rnd() % 0xfffffffffffu;
}

/* The decoded words of an accepting decoder for the candidate the law is at. */
static uint64_t env_decoded_word(uint64_t w, uint64_t candidate) {
    if (w == 1) return 1;
    if (w == 11) return env_count;
    if (w == 14) return 1;
    if (w == 15) return 0;
    if (w == 16) return candidate;
    if (w == 17) return env_highest;
    return env_wild ? quickproof_rnd() : env_any();
}

static void env_plan(void) {
    env_planned = 1;
    /* 60% boot_allocate's sequence; the rest each step alone. */
    static const int calls[20] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, 4, 5, 6, 6};
    env_call = (uint32_t)calls[env_r(20)];
    env_take_next = env_r(2) ? 0 : env_r(4) ? 1 : (uint32_t)quickproof_rnd() | 1u;
    env_value_kind = (int)env_r(8);
    env_wild = (int)env_r(2);
    env_count = env_r(4) ? 1 + env_r(256) : quickproof_rnd();
    env_highest = env_r(4) ? env_r(0x100000) : quickproof_rnd();
    /* The accepted candidates: mostly among the first 16, sometimes anywhere, rarely none. */
    unsigned k = (unsigned)env_r(32);
    env_accept = k < 24 ? (long)env_r(16) : k < 30 ? (long)env_r(4096) : k < 31 ? 4095 : -1;
    env_accept2 = env_accept >= 0 && env_accept < 4095 ?
        env_accept + 1 + (long)(env_r(2) ? env_r(8) : env_r((uint64_t)(4095 - env_accept))) : -1;
    if (env_accept2 > 4095) env_accept2 = -1;
#ifdef GP_RUNS
    env_accept = (long)env_r(4);
    env_accept2 = env_accept + 1 + (long)env_r(3);
#endif
    env_frame = env_accept >= 0 ? (uint64_t)env_accept : 4096;
    env_frame2 = env_accept2 >= 0 ? (uint64_t)env_accept2 : 4096;
    env_reject = -1;
    env_blocks[0] = env_blocks[1] = env_blocks[2] = -1;
    env_random_at = env_r(8) == 0 ? (long)env_r(env_r(2) ? 64 : 2000) : -1;
    /* The perturbations that apply to each function, each about as likely as the others. */
    static const int allocate_targets[14] = {ENV_NONE, ENV_NONE, ENV_OVERLAY, ENV_TERMINAL, ENV_TERMINAL, ENV_DECODER,
                                             ENV_CONSUME, ENV_AUTHORITY, ENV_AUTHORITY, ENV_SCRUB, ENV_PUBLICATION,
                                             ENV_UNPUBLISHED, ENV_RESCAN, ENV_RESCAN};
    static const int terminal_targets[4] = {ENV_NONE, ENV_OVERLAY, ENV_TERMINAL, ENV_TERMINAL};
    static const int select_targets[4] = {ENV_NONE, ENV_DECODER, ENV_CONSUME, ENV_CONSUME};
    static const int cross_targets[4] = {ENV_NONE, ENV_AUTHORITY, ENV_AUTHORITY, ENV_AUTHORITY};
    static const int publication_targets[4] = {ENV_NONE, ENV_PUBLICATION, ENV_PUBLICATION, ENV_PUBLICATION};
    static const int rescan_targets[4] = {ENV_NONE, ENV_UNPUBLISHED, ENV_RESCAN, ENV_RESCAN};
    switch (env_call) {
    case CALL_ALLOCATE: env_target = allocate_targets[env_r(14)]; break;
    case CALL_TERMINAL: env_target = terminal_targets[env_r(4)]; break;
    case CALL_SELECT: env_target = select_targets[env_r(4)]; break;
    case CALL_CROSS_CHECK: env_target = cross_targets[env_r(4)]; break;
    case CALL_SCRUB: env_target = env_r(2) ? ENV_NONE : ENV_SCRUB; break;
    case CALL_PUBLICATION: env_target = publication_targets[env_r(4)]; break;
    default: env_target = rescan_targets[env_r(4)]; break;
    }
    if ((env_target == ENV_UNPUBLISHED || env_target == ENV_RESCAN) && env_call == CALL_ALLOCATE && !env_take_next)
        env_take_next = 1;
    switch (env_target) {
    case ENV_OVERLAY:   /* one to three blocks, the first, the last or any */
        for (int i = 0; i < 1 + (int)env_r(3); ++i)
            env_blocks[i] = env_r(3) == 0 ? 0 : env_r(2) ? 63 : (long)env_r(64);
        break;
    case ENV_TERMINAL: {
        static const int words[8] = {0, 1, 2, 3, 3, 4, 5, 5};
        env_word = words[env_r(8)];
        break;
    }
    case ENV_DECODER:   /* at the accepted candidate or before it, or at the second */
        env_reject = env_accept < 0 ? (long)env_r(4096) : env_r(2) ? env_accept : (long)env_r((uint64_t)env_accept + 1);
        if (env_take_next && env_accept2 >= 0 && env_r(3) == 0) env_reject = env_accept2;
#ifdef GP_RUNS
        if (env_reject > 6) env_reject = 6;
#endif
        break;
    case ENV_CONSUME: {   /* the frame the consumer accepts: another than the candidate, or the boundary */
        static const uint64_t frames[6] = {4095, 0, 1, 2048, 4094, 7};
        env_frame = env_r(2) ? frames[env_r(6)] : env_near(env_frame) % 4096;
        if (env_r(3) == 0) env_frame2 = env_r(2) ? env_frame : env_near(env_frame2) % 4096;
        break;
    }
    case ENV_AUTHORITY: {   /* the nomination, the target, the entry count, the highest frame, usable, blocked,
                               the manifest's answer, or no frame */
        static const int words[8] = {3, 16, 11, 17, 14, 15, 0, 99};
        env_word = words[env_r(8)];
#ifdef GP_RUNS
        /* No frame takes a scan of every candidate in boot_allocate's sequence. */
        if (env_word == 99 && env_call == CALL_ALLOCATE) env_word = 16;
#endif
        break;
    }
    case ENV_PUBLICATION:
        env_word = (int)env_r(5);
        break;
    case ENV_UNPUBLISHED:   /* no next frame (natively: a scan to the last candidate), or one not above the
                               selected one */
#ifndef GP_RUNS
        if (env_r(2)) env_accept2 = -1;
#endif
        env_frame2 = env_accept2 < 0 ? 4096 : env_r(2) ? env_frame : env_frame - env_r(env_frame + 1);
        break;
    case ENV_RESCAN: {   /* the decoder's rejection, the entry count, the highest frame, the target, the status,
                            usable, blocked or the manifest's answer */
        static const int words[8] = {-1, 11, 17, 16, 1, 14, 15, 99};
        env_word = words[env_r(8)];
        break;
    }
    default:
        break;
    }
    /* main's inputs: random, then shaped for the call. */
    for (int i = 0; i < DRAWS; ++i) env_input[i] = env_any();
    env_input[DRAW_CALL] = env_call;
    env_input[DRAW_TAKE_NEXT] = env_take_next;
    env_input[DRAW_DECODED + 1] = env_r(8) ? 1 : env_any();
    env_input[DRAW_DECODED + 2] = env_r(8) ? 0 : env_any();
    env_input[DRAW_DECODED + 11] = env_count;
    env_input[DRAW_DECODED + 17] = env_highest;
    uint64_t selected = env_r(4) ? env_r(4096) : (uint64_t[]){0, 4095, 4096, 0xffffffffffffffffu}[env_r(4)];
    env_input[DRAW_SELECTED] = selected;
    env_input[DRAW_SELECTED_MANIFEST] = env_call == CALL_CROSS_CHECK ? 1 : env_any();
    if (env_call == CALL_CROSS_CHECK) {
        env_input[DRAW_TERMINAL + 3] = selected;
        for (int w = 0; w < WORDS; ++w)
            env_input[DRAW_STATES + w] = env_decoded_word((uint64_t)w, selected);
        if (env_target == ENV_AUTHORITY) {
            if (env_word == 3) env_input[DRAW_TERMINAL + 3] = env_near(selected);
            else if (env_word == 0) env_input[DRAW_SELECTED_MANIFEST] = env_near(1);
            else if (env_word == 99) env_input[DRAW_SELECTED] = 4096 + env_r(2) * quickproof_rnd();
            else env_input[DRAW_STATES + env_word] = env_near(env_input[DRAW_STATES + env_word]);
        }
    }
    /* The rescan alone: a next frame above the published one, near the bounds. */
    uint64_t next = env_r(4) ? 1 + env_r(4095) : (uint64_t[]){4095, 1, 4096, 0xffffffffffffffffu}[env_r(4)];
    uint64_t published = next == 0 ? 0 : next - 1 - (env_r(2) ? 0 : env_r(next));
    if (env_call == CALL_RESCAN && env_target == ENV_UNPUBLISHED) {
        static const int kinds[4] = {0, 1, 2, 3};
        switch (kinds[env_r(4)]) {
        case 0: next = 4096; break;
        case 1: published = next; break;
        case 2: published = next + env_r(4096); break;
        default: next = 4096 + quickproof_rnd() % 0xffffffffu; break;
        }
    }
    env_input[DRAW_PUBLISHED] = published;
    env_input[DRAW_NEXT] = next;
}

/* The accepting answer to the call the law is at, before any perturbation. */
static uint64_t env_accepting(void) {
    struct law *m = &law;
    uint64_t w = m->word;
    switch (m->expect) {
    case EXPECT_MANIFEST:
        if (w == 1) return 1;
        if (w == 2) return 0;
        return quickproof_rnd();
    case EXPECT_FREE:
        return quickproof_rnd();
    case EXPECT_FINISH:
        if (w == 0 || w == 1 || w == 4) return 1;
        if (w == 2) return 0;
        if (w == 3) return env_call == CALL_ALLOCATE ? env_frame : env_r(4096);
        if (w == 5) return m->decoded[11];
        return quickproof_rnd();
    case EXPECT_DECODE:
        if (w == WORDS) return 0;   /* the status */
        return env_decoded_word(w, m->candidate);
    case EXPECT_CANDIDATE:
        if (m->step == STEP_RESCAN) return 1;
        if ((long)m->candidate == env_accept || (long)m->candidate == env_accept2) return 1;
        return env_r(2) ? 1 : env_any();
    case EXPECT_CONSUME:
        if (m->scan == 0 && (long)m->candidate == env_accept) return env_frame;
        if (m->scan == 1 && (long)m->candidate == env_accept2) return env_frame2;
        return env_reject_frame();
    case EXPECT_SCRUB:
        return 1;
    case EXPECT_AUTHORITY:
        if (w == 0 || w == 1) return 1;
        if (w == 2) return 0;
        if (w == 3) return m->selected;
        if (w == 4) return m->selected + 1;
        return quickproof_rnd();
    default:
        return quickproof_rnd();
    }
}

/* The answer to the call the law is at. */
static uint64_t env_answer(void) {
    struct law *m = &law;
    uint64_t v = env_accepting();
    long w = (long)m->word;
    int selected_decode = m->expect == EXPECT_DECODE && m->step == STEP_SELECT && m->scan == 0 &&
                          (long)m->candidate == env_accept;
    switch (env_target) {
    case ENV_OVERLAY:
        if (m->expect == EXPECT_MANIFEST && w < 3 &&
            ((long)m->block == env_blocks[0] || (long)m->block == env_blocks[1] || (long)m->block == env_blocks[2]))
            v = env_r(2) ? env_near(v) : (w == 1 ? 2 : 1);
        break;
    case ENV_TERMINAL:
        if (m->expect == EXPECT_FINISH && w == env_word) v = w == 3 ? 4096 + env_r(2) * quickproof_rnd() : env_near(v);
        break;
    case ENV_DECODER:
        if (m->expect == EXPECT_DECODE && m->step == STEP_SELECT && (long)m->candidate == env_reject && w == WORDS)
            v = 1 + env_r(60);
        break;
    case ENV_AUTHORITY:
        if (env_call == CALL_ALLOCATE) {
            if (env_word == 3 && m->expect == EXPECT_FINISH && w == 3) v = env_near(v) % 8192;
            else if (env_word == 0 && m->expect == EXPECT_CANDIDATE && m->step == STEP_SELECT &&
                     (long)m->candidate == env_accept)
                v = env_near(1);
            else if (env_word == 99 && m->expect == EXPECT_CONSUME) v = env_reject_frame();
            else if (selected_decode && w == env_word) v = env_near(v);
        }
        break;
    case ENV_SCRUB:
        if (m->expect == EXPECT_SCRUB) v = (uint64_t[]){0, 2, 0xffffffffu, 0x100000001u}[env_r(4)];
        break;
    case ENV_PUBLICATION:
        if (m->expect == EXPECT_AUTHORITY && w == env_word) v = env_near(v);
        break;
    case ENV_RESCAN:
        if (m->step == STEP_RESCAN && m->expect == EXPECT_DECODE && env_word >= 0 && w == env_word) v = env_near(v);
        if (m->step == STEP_RESCAN && m->expect == EXPECT_DECODE && env_word < 0 && w == WORDS) v = 1 + env_r(60);
        if (m->step == STEP_RESCAN && m->expect == EXPECT_CANDIDATE && env_word == 99) v = env_near(1);
        break;
    default:
        break;
    }
    return v;
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    if (env_have_lo) {
        env_have_lo = 0;
        return (uint32_t)env_pending_lo;
    }
    uint64_t v;
    if (!law.running) {
        unsigned long k = env_inputs_drawn++;
        v = k < DRAWS ? env_input[k] : quickproof_rnd();
    } else {
        v = env_answer();
        if (env_answers++ == env_random_at) {
            v = env_r(2) ? quickproof_rnd() : env_r(4);
#ifdef GP_RUNS
            /* A consumer that rejects the planned candidate would scan every candidate. */
            if (law.expect == EXPECT_CONSUME) v = env_r(4);
#endif
        }
    }
    env_pending_lo = v & 0xffffffffu;
    env_have_lo = 1;
    return (uint32_t)(v >> 32);
}

uint8_t nondet_u8(void) { return (uint8_t)quickproof_rnd(); }

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
