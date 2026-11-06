/* Value distributions of the law consumer_obligations for native and interpreter runs (not part of any theorem).
 * The law draws the span length (nondet_size), the span (nondet_bytes), six observation words (two u32 each), three
 * NULL choices (u8), then two u32 per answer of the adversarial Lean: 16 per byte, 5 for the NMI policy, 6 for the
 * finish.  Uniform answers would reject the first transition every time, so this plan answers what an accepting
 * Lean would, and makes most spans well-formed records (local APIC, I/O APIC and NMI records tiling the span).  Each
 * run then perturbs at most one place: one stream projection, the record framing, one policy word or one finish
 * word, with the values next to each check's boundary, so that runs reach every check and every status.  One run in
 * six is a span of 4 to 8 NMI records only, more than the four the consumer keeps.  It tracks the values it drew
 * itself to know the expected answers. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

enum { NONE, STREAM, RECORDS, POLICY, FINISH };
static int env_target;
static unsigned long env_target_index, env_target_word, env_target_pick, env_second_word, env_second_pick;
static int env_second;   /* a second word perturbed too (policy and finish) */
static int env_nmi_heavy;  /* a span of 4 to 8 NMI records only (more than the four the consumer keeps) */
static int env_probe;    /* policy: word 1 wrong (status 5) with one range word at its boundary */
static size_t env_length;
static uint8_t env_bytes[256];
static uint64_t env_obs[6];
static unsigned long env_u32_calls;
static uint64_t env_pending_lo;
static int env_have_lo;
static uint64_t env_state6;

size_t nondet_size(void) {
    static const int targets[20] = {NONE, NONE, STREAM, STREAM, STREAM, RECORDS, RECORDS, POLICY, POLICY, POLICY,
                                    POLICY, POLICY, POLICY, POLICY, FINISH, FINISH, FINISH, FINISH, FINISH, FINISH};
    env_target = targets[env_r(20)];
    static const unsigned long checked[5] = {0, 1, 2, 3, 15};   /* the stream projections the consumer checks */
    static const unsigned long finish_word[10] = {1, 1, 1, 1, 1, 0, 2, 3, 4, 5};   /* word 1 names statuses 4 */
    env_target_word = env_target == STREAM ? checked[env_r(5)] : env_target == POLICY ? env_r(5) :
                      finish_word[env_r(10)];
    env_target_pick = env_r(4);
    env_second = env_r(4) == 0;
    env_second_word = env_target == POLICY ? env_r(5) : env_r(6);
    env_second_pick = env_r(4);
    env_probe = env_target == POLICY && env_r(2) == 0 ? 1 + (int)env_r(7) : 0;
    unsigned k = (unsigned)env_r(16);
    env_nmi_heavy = env_r(6) == 0;
    if (env_nmi_heavy) env_length = 6 * (4 + (size_t)env_r(5));
    else if (k == 0) env_length = 0;
    else if (k == 1) env_length = (size_t)(65536 - 44 + env_r(3));
    else env_length = 1 + (size_t)env_r(env_r(2) ? 8 : 48);   /* short spans reach the later stages more often */
    env_target_index = env_length ? env_r(env_length) : 0;
    return env_length;
}

void nondet_bytes(uint8_t *buf, size_t n) {
    int records = env_r(5) != 0 || env_target == RECORDS || env_nmi_heavy;
    size_t at = 0;
    while (at < n) {
        if (!records) { buf[at] = (uint8_t)quickproof_rnd(); ++at; continue; }
        static const uint8_t kinds[3] = {0, 1, 4}, lengths[3] = {8, 12, 6};
        unsigned k = env_nmi_heavy ? 2 : (unsigned)env_r(3);
        size_t len = lengths[k];
        if (len > n - at) len = n - at;
        for (size_t i = 0; i < len; ++i) buf[at + i] = (uint8_t)quickproof_rnd();
        buf[at] = len == lengths[k] ? kinds[k] : 0;
        if (len >= 2) buf[at + 1] = (uint8_t)len;
        at += len;
    }
    if (env_target == RECORDS && n >= 2) {   /* break the framing at the first record */
        static const uint8_t framing[4][2] = {{4, 4}, {4, 8}, {0, 1}, {0, 255}};
        buf[0] = framing[env_target_pick][0];
        buf[1] = framing[env_target_pick][1];
    }
    for (size_t i = 0; i < n && i < sizeof env_bytes; ++i) env_bytes[i] = buf[i];
}

uint8_t nondet_u8(void) {
    return (uint8_t)(env_r(10) == 0 ? 0 : 1);   /* each pointer NULL with probability 1/10 */
}

/* The values next to each check's boundary. */
static uint64_t env_near(uint64_t accepted, unsigned long pick) {
    static const int64_t delta[4] = {1, -1, 2, 3};
    return accepted + (uint64_t)delta[pick];
}

static uint64_t env_answer(unsigned long j) {
    unsigned long stream = 16ul * env_length;
    if (j < stream) {
        unsigned long byte = j / 16, word = j % 16;
        uint64_t offset = 44 + byte, v;
        if (word == 0) v = 1;
        else if (word == 1) v = byte + 1 == env_length ? 3 : 1;
        else if (word == 2) v = 0;
        else if (word == 3) v = offset + 1;
        else if (word == 15) v = byte < sizeof env_bytes ? env_bytes[byte] : 0;
        else v = env_r(8);
        if (env_target == STREAM && byte == env_target_index && word == env_target_word)
            v = word == 1 && env_target_pick == 0 ? 2 : env_near(v, env_target_pick);
        if (word == 9) env_state6 = v;   /* projection 9 is state word 6 */
        return v;
    }
    j -= stream;
    if (j < 5) {
        static const uint64_t policy[5] = {1, 1, 0, 1, 4};
        uint64_t v = policy[j];
        if (env_target == POLICY && j == env_target_word) v = env_near(v, env_target_pick);
        if (env_target == POLICY && env_second && j == env_second_word && j != env_target_word)
            v = env_near(v, env_second_pick);
        if (env_probe) {   /* word 1 is 0, word 2 the detail 88, and at most one range word just past its bound */
            static const uint64_t range[7][2] = {{5, 0}, {0, 0}, {0, 2}, {3, 2}, {3, 0}, {4, 5}, {4, 3}};
            v = policy[j];
            if (j == 1) v = 0;
            if (j == 2) v = 88;
            if (range[env_probe - 1][0] == j) v = range[env_probe - 1][1];
        }
        if (env_target == POLICY && j == 2 && env_target_word == 1) v = 88;   /* the detail of status 5 */
        return v;
    }
    j -= 5;
    uint64_t v = j == 0 ? 1 : j == 1 ? 1 : j == 2 ? env_obs[0] : j == 3 ? env_state6 : j == 4 ? env_obs[3] : 0;
    static const uint64_t status[4] = {2, 5, 3, 0};
    if (env_target == FINISH && j == env_target_word)
        v = j == 1 ? status[env_target_pick] : env_near(v, env_target_pick);
    if (env_target == FINISH && env_second && j == env_second_word && j != env_target_word)
        v = j == 1 ? status[env_second_pick] : env_near(v, env_second_pick);
    return v;
}

uint32_t nondet_u32(void) {
    unsigned long k = env_u32_calls++;
    if (k < 12) {   /* the observation: executing, cpuid_edx, available, apic_base, sample_id, routing */
        uint64_t v = k / 2 == 0 ? env_r(4) : k / 2 == 2 ? env_r(2) : k / 2 == 5 ? (env_r(8) == 0) : quickproof_rnd();
        if (k % 2 == 0) { env_obs[k / 2] = v; return (uint32_t)(v >> 32); }
        return (uint32_t)env_obs[k / 2];
    }
    if (env_have_lo) { env_have_lo = 0; return (uint32_t)env_pending_lo; }
    uint64_t v = env_r(5000) == 0 ? quickproof_rnd() : env_answer((k - 12) / 2);
    env_pending_lo = v & 0xffffffffu;
    env_have_lo = 1;
    return (uint32_t)(v >> 32);
}
