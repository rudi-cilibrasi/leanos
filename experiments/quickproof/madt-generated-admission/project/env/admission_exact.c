/* Value distributions of the law admission_exact for native and interpreter runs (not part of any theorem).
 * The law draws the function to call (u8), the copy's length and the executing APIC ID (u32), the copy
 * (nondet_bytes), ten result arguments (two u32 each) and the prior APIC ID record (u32), then two u32 per answer
 * of the adversarial Lean.  Uniform answers would reject the first transition every time.  So this plan makes
 * most copies well-formed MADTs (local APIC, I/O APIC, override and NMI records after a 44-byte header) and
 * answers what an accepting Lean would, reading the law's model (harness/admission_exact.h) for the step it is
 * at: the checked words as the header accepts them, small arbitrary values in every word the header carries
 * without checking, and at the last transition the final state an admission needs.  Each run draws one of 49
 * scenarios, so that each check's boundary gets 6 to 12 of the 300 seeds a mutant runs: no perturbation; one
 * answer of any value; the copy's length or the executing ID at the entries' bounds; one checked word of one
 * envelope or entry transition (mostly the last), with the values next to its check's boundary; one word of the
 * envelope's or the entries' final state; an accepted seen set in one limb only; one word of the result; or
 * accepting result answers against APIC ID arguments at the result's checks (2^32 - 1, 2^32 or more, or two
 * IDs that differ).  It then calls a function that reaches the scenario's check, the admission half the time.
 * One run in 64 has a copy of 64 KiB.  Under the interpreter (GP_RUNS defined), whose budget per seed its 23
 * calls per byte exceed, those copies have 45 to 60 bytes instead, and the others at most six records. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"
#include "../harness/admission_exact.h"

extern uint64_t quickproof_rnd(void);

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

enum { ENV_NONE, ENV_RANDOM, ENV_BOUNDS, ENV_ENVELOPE, ENV_ENVELOPE_FINAL, ENV_ENTRIES, ENV_ENTRIES_FINAL, ENV_SEEN,
       ENV_RESULT, ENV_RESULT_IDS };

static int env_planned, env_target, env_value;
static uint32_t env_call, env_length, env_executing, env_records;
static uint8_t env_kind[12], env_size[12];
static uint64_t env_at, env_word, env_word9, env_seen_shape;
static uint64_t env_args[10];
static unsigned long env_u32_calls, env_answers;
static long env_random_at;
static uint64_t env_pending_lo;
static int env_have_lo;

/* The scenarios: a target and the word (or case) it perturbs, twice for a check that only that word reaches.
   Entries-final word 11 empties the seen set; seen case k admits an ID whose bit is the only one, in limb k;
   a transition word of 255 is one of the five checked words of that transition. */
#define ENV_SCENARIOS 49
static const uint8_t env_scenarios[ENV_SCENARIOS][2] = {
    {ENV_NONE, 0}, {ENV_RANDOM, 0},
    {ENV_BOUNDS, 0}, {ENV_BOUNDS, 0}, {ENV_BOUNDS, 1}, {ENV_BOUNDS, 2}, {ENV_BOUNDS, 3}, {ENV_BOUNDS, 3},
    {ENV_BOUNDS, 4}, {ENV_BOUNDS, 5},
    {ENV_ENVELOPE, 255}, {ENV_ENVELOPE, 255},
    {ENV_ENVELOPE_FINAL, 4}, {ENV_ENVELOPE_FINAL, 4}, {ENV_ENVELOPE_FINAL, 5},
    {ENV_ENTRIES, 255}, {ENV_ENTRIES, 255},
    {ENV_ENTRIES_FINAL, 4}, {ENV_ENTRIES_FINAL, 4}, {ENV_ENTRIES_FINAL, 5}, {ENV_ENTRIES_FINAL, 5},
    {ENV_ENTRIES_FINAL, 6}, {ENV_ENTRIES_FINAL, 6}, {ENV_ENTRIES_FINAL, 7}, {ENV_ENTRIES_FINAL, 7},
    {ENV_ENTRIES_FINAL, 8}, {ENV_ENTRIES_FINAL, 8}, {ENV_ENTRIES_FINAL, 9}, {ENV_ENTRIES_FINAL, 10},
    {ENV_ENTRIES_FINAL, 10}, {ENV_ENTRIES_FINAL, 11},
    {ENV_SEEN, 0}, {ENV_SEEN, 1}, {ENV_SEEN, 1}, {ENV_SEEN, 2}, {ENV_SEEN, 2}, {ENV_SEEN, 3}, {ENV_SEEN, 3},
    {ENV_RESULT, 0}, {ENV_RESULT, 1}, {ENV_RESULT, 1}, {ENV_RESULT, 2}, {ENV_RESULT, 3},
    {ENV_RESULT_IDS, 0}, {ENV_RESULT_IDS, 0}, {ENV_RESULT_IDS, 1}, {ENV_RESULT_IDS, 1}, {ENV_RESULT_IDS, 2},
    {ENV_RESULT_IDS, 3}};

static void env_plan(void) {
    env_planned = 1;
    unsigned scenario = (unsigned)env_r(ENV_SCENARIOS);
    env_target = env_scenarios[scenario][0];
    env_word = env_scenarios[scenario][1];
    if (env_word == 255) {
        static const uint8_t checked[2][5] = {{0, 1, 2, 3, 6}, {0, 1, 2, 3, 15}};
        env_word = checked[env_target == ENV_ENTRIES][env_r(5)];
    }
    env_value = (int)env_r(8);
    /* The function: one that reaches the target, the admission half the time. */
    static const uint32_t calls[4] = {CALL_ENVELOPE, CALL_ENTRIES, CALL_RESULT, CALL_ADMISSION};
    int admission = env_r(2) == 0;
    switch (env_target) {
    case ENV_ENVELOPE: case ENV_ENVELOPE_FINAL: env_call = admission ? CALL_ADMISSION : CALL_ENVELOPE; break;
    case ENV_BOUNDS: case ENV_ENTRIES: case ENV_ENTRIES_FINAL: case ENV_SEEN:
        env_call = admission ? CALL_ADMISSION : CALL_ENTRIES;
        break;
    case ENV_RESULT: env_call = admission ? CALL_ADMISSION : CALL_RESULT; break;
    case ENV_RESULT_IDS: env_call = CALL_RESULT; break;
    default: env_call = calls[env_r(4)]; break;
    }
    /* The copy's length: mostly a header and one to twelve records, sometimes a length next to a bound. */
    unsigned k = (unsigned)env_r(64);
    if (k == 0) {
#ifdef GP_RUNS
        env_length = 45 + (uint32_t)env_r(16);
#else
        env_length = 65536 - (uint32_t)env_r(2);
#endif
    } else if (k < 5) {
        static const uint32_t edges[8] = {0, 1, 8, 36, 43, 44, 45, 46};
        env_length = edges[env_r(8)];
    } else {   /* a header and one to twelve records */
        static const uint8_t kinds[5] = {0, 0, 1, 2, 4}, sizes[5] = {8, 8, 12, 10, 6};
#ifdef GP_RUNS
        env_records = 1 + (uint32_t)env_r(6);   /* within the interpreter's budget per seed */
#else
        env_records = 1 + (uint32_t)env_r(12);
#endif
        env_length = 44;
        for (uint32_t r = 0; r < env_records; ++r) {
            unsigned c = (unsigned)env_r(5);
            env_kind[r] = kinds[c];
            env_size[r] = sizes[c];
            env_length += sizes[c];
        }
    }
    /* The executing APIC ID: mostly small, sometimes 255, the largest the entries accept; in a seen case k,
       one of limb k's (and for limb 0 often ID 0, whose seen set is 1). */
    unsigned e = (unsigned)env_r(8);
    env_executing = e == 0 ? 255 : e < 3 ? (uint32_t)env_r(256) : (uint32_t)env_r(4);
    if (env_target == ENV_SEEN)
        env_executing = env_word == 0 && env_r(2) ? 0 : 64 * (uint32_t)env_word + (uint32_t)env_r(64);
    if (env_target == ENV_BOUNDS) {
        switch (env_word) {
        case 0: env_length = 44; break;                                   /* the largest the entries refuse */
        case 1: env_length = env_r(2) ? 43 : 0; break;
        case 2: env_length = 45; break;                                   /* the smallest they accept */
        case 3: env_executing = 255; break;                               /* the largest ID they accept */
        case 4: env_executing = 256; break;
        default: env_executing = env_r(2) ? 0xffffffffu : 0x100u + (uint32_t)env_r(256); break;
        }
    }
    /* The result's arguments: a root selection and copy counts, one MADT, an accepted admission and two equal
       APIC IDs; the ID cases make them 2^32 - 1, 2^32 or more, or differ, with answers that accept. */
    env_args[0] = 1 + env_r(2);
    env_args[1] = 0x000e0000u + 16 * env_r(4096);
    env_args[2] = env_r(16) == 0 ? env_args[1] + 16 : env_args[1];
    env_args[3] = 1 + env_r(8);
    env_args[4] = env_args[3];
    env_args[5] = 1;
    env_args[6] = 1;
    env_args[7] = 0;
    env_args[8] = env_executing;
    env_args[9] = env_executing;
    env_word9 = 0;
    if (env_target == ENV_RESULT_IDS) {
        static const uint64_t ids[4] = {0x100000000u, 0x100000000u + 3, 0xffffffffffffffffu, 0x1000000ffu};
        switch (env_word) {
        case 0: env_args[8] = env_args[9] = 0xffffffffu; break;
        case 1: env_args[8] = env_args[9] = ids[env_r(4)]; break;
        case 2: env_args[8] = env_args[9] + 1 + env_r(2); env_word9 = env_r(2); break;
        default: env_args[9] = env_args[8] + 1 + env_r(2); env_word9 = env_r(2); break;
        }
    }
    env_seen_shape = env_target == ENV_SEEN ? 0 : env_r(4);
    env_random_at = env_target == ENV_RANDOM ? (long)env_r(2000) : -1;
}

/* A transition to perturb: mostly the last, else any. */
static void env_choose_at(void) {
    struct law *m = &law;
    uint64_t first = m->expect == EXPECT_ENTRIES ? 44 : 0;
    uint64_t span = m->length > first ? m->length - first : 1;
    env_at = env_r(2) ? m->length - 1 : first + env_r(span);
}

/* A value next to the boundary of the check of `word`, whose accepted value is `v`. */
static uint64_t env_near(uint64_t v) {
    static const uint64_t delta[8] = {1, (uint64_t)-1, 2, 0x100000000u, (uint64_t)-2, 3, 0x8000000000000000u, 256};
    return v + delta[env_value];
}

static uint64_t env_envelope_answer(void) {
    struct law *m = &law;
    uint64_t i = m->at, w = m->word, last = i + 1 == m->length;
    if (i == 0 && w == 0 && (env_target == ENV_ENVELOPE || env_target == ENV_ENVELOPE_FINAL)) {
        env_choose_at();
        if (env_target == ENV_ENVELOPE_FINAL) env_at = m->length - 1;
    }
    uint64_t v = w == 0 ? 1 : w == 1 ? (last ? 3 : 1) : w == 2 ? 0 : w == 3 ? i + 1 :
                 w == 4 ? (last ? m->length : env_r(4) ? i : env_r(65536)) :
                 w == 5 ? (last ? 0 : env_r(256)) : m->copy[i];
    if ((env_target != ENV_ENVELOPE && env_target != ENV_ENVELOPE_FINAL) || i != env_at || w != env_word)
        return v;
    if (w == 1) {   /* the rejection status, the other accepting status, or near them */
        static const uint64_t status[8] = {2, 0, 4, 0x100000001u, 2, 0x100000003u, 2, 5};
        return env_value == 1 ? (last ? 1 : 3) : status[env_value];
    }
    if (w == 2) {
        static const uint64_t errors[8] = {55, 56, 57, 58, 59, 1, 0x100000000u, 0xffffffffffffffffu};
        return errors[env_value];
    }
    if (w == 5) {
        static const uint64_t sums[8] = {1, 255, 256, 0x100000000u, 0x80, 2, 0xffffffffffffffffu, 0x100};
        return sums[env_value];
    }
    return env_near(v);
}

static uint64_t env_entries_answer(void) {
    struct law *m = &law;
    uint64_t k = m->at, w = m->word, last = k + 1 == m->length;
    if (k == 44 && w == 0 && (env_target == ENV_ENTRIES || env_target == ENV_ENTRIES_FINAL)) {
        env_choose_at();
        if (env_target == ENV_ENTRIES_FINAL) env_at = m->length - 1;
    }
    uint64_t exec = m->executing, v;
    if (w == 0) v = 1;
    else if (w == 1) v = last ? 3 : 1;
    else if (w == 2) v = 0;
    else if (w == 3) v = k + 1;
    else if (w == 15) v = m->copy[k];
    else if (!last) v = env_r(4) ? env_r(16) : env_r(1u << 20);   /* carried unchecked */
    else if (w <= 8) v = 0;          /* no record open */
    else if (w == 9) v = 1;          /* one enabled APIC */
    else if (w == 10) v = exec;      /* the executing one */
    else {                           /* the seen set: the admitted ID's bit, perhaps others */
        uint64_t limb = w - 11;
        v = limb == exec / 64 ? (uint64_t)1 << (exec % 64) : 0;
        if (env_seen_shape == 1) v |= env_r(2) ? (uint64_t)1 << env_r(64) : 0;
        if (env_seen_shape == 2 && limb == (exec / 64 + 1) % 4) v = (uint64_t)1 << env_r(64);
    }
    if ((env_target != ENV_ENTRIES && env_target != ENV_ENTRIES_FINAL) || k != env_at)
        return v;
    if (env_target == ENV_ENTRIES_FINAL && env_word >= 11)
        return w >= 11 && w <= 14 ? 0 : v;   /* an empty seen set */
    if (w != env_word) return v;
    if (w == 1) {
        static const uint64_t status[8] = {2, 0, 4, 0x100000001u, 2, 0x100000003u, 2, 5};
        return env_value == 1 ? (last ? 1 : 3) : status[env_value];
    }
    if (w == 2) {
        static const uint64_t errors[8] = {69, 70, 72, 74, 75, 76, 1, 0x100000000u};
        return errors[env_value];
    }
    if (w >= 4 && w <= 8) {
        static const uint64_t open[8] = {1, 7, 8, 0x100000000u, 0x8000000000000000u, 2, 12, 0xff};
        return open[env_value];
    }
    if (w == 9) {
        static const uint64_t count[8] = {0, 2, 256, 0x100000001u, 0, 3, 2, 0xffffffffffffffffu};
        return count[env_value];
    }
    if (w == 10) {
        /* mostly another ID of 0..255, else one above 255 */
        static const uint64_t ids[8] = {1, 2, 64, 3, 0x100, 0x100000000u, 0, 0};
        if (env_value == 6) return exec == 255 ? 254 : 255;
        if (env_value == 7) return exec == 0 ? 1 : exec - 1;
        return (exec + ids[env_value]) % (env_value < 4 ? 256 : 0x10000000000u);
    }
    return env_near(v);
}

static uint64_t env_result_answer(void) {
    struct law *m = &law;
    uint64_t w = m->word;
    uint64_t v = w == 0 ? 1 : w == 1 ? 1 : w == 2 ? 0 : m->args[env_word9 ? 9 : 8];
    if (env_target != ENV_RESULT || w != env_word) return v;   /* the ID cases accept */
    if (w == 1) {
        static const uint64_t status[8] = {2, 0, 3, 0x100000001u, 2, 2, 0, 0xffffffffffffffffu};
        return status[env_value];
    }
    if (w == 2) {
        static const uint64_t errors[8] = {50, 51, 52, 53, 54, 1, 0x100000000u, 0xffffffffffffffffu};
        return errors[env_value];
    }
    if (w == 3 && env_value >= 6) return m->args[9];
    return env_near(v);
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    unsigned long k = env_u32_calls++;
    if (k == 0) return env_length;
    if (k == 1) return env_executing;
    if (k < 22) {   /* the result's ten arguments, high word first */
        uint64_t v = env_args[(k - 2) / 2];
        return (uint32_t)(k % 2 == 0 ? v >> 32 : v);
    }
    if (k == 22) return (uint32_t)quickproof_rnd();   /* the prior APIC ID record */
    if (env_have_lo) {
        env_have_lo = 0;
        return (uint32_t)env_pending_lo;
    }
    uint64_t v = law.expect == EXPECT_ENVELOPE ? env_envelope_answer() :
                 law.expect == EXPECT_ENTRIES ? env_entries_answer() :
                 law.expect == EXPECT_RESULT ? env_result_answer() : quickproof_rnd();
    if ((long)env_answers++ == env_random_at) v = quickproof_rnd();
    env_pending_lo = v & 0xffffffffu;
    env_have_lo = 1;
    return (uint32_t)(v >> 32);
}

uint8_t nondet_u8(void) {
    if (!env_planned) env_plan();
    return (uint8_t)(env_call == CALL_ADMISSION && env_r(2) ? 3 + env_r(253) : env_call);
}

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

/* The copy: the planned records after a 44-byte MADT header (signature, length, checksum), or any bytes. */
void nondet_bytes(uint8_t *buf, size_t n) {
    if (!env_planned) env_plan();
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
    if (n < 44 || env_r(8) == 0) return;
    size_t at = 44;
    for (uint32_t r = 0; r < env_records && at + env_size[r] <= n; ++r) {
        buf[at] = env_kind[r];
        buf[at + 1] = env_size[r];
        if (env_kind[r] == 0) buf[at + 4] = (uint8_t)env_r(4);   /* flags: enabled, online capable */
        at += env_size[r];
    }
    buf[0] = 'A'; buf[1] = 'P'; buf[2] = 'I'; buf[3] = 'C';
    for (int b = 0; b < 4; ++b) buf[4 + b] = (uint8_t)(n >> (8 * b));
    buf[9] = 0;
    uint8_t sum = 0;
    for (size_t i = 0; i < n; ++i) sum = (uint8_t)(sum + buf[i]);
    buf[9] = (uint8_t)(0 - sum);
}
