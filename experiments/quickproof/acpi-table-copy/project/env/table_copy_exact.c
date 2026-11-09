/* Value distributions of the law table_copy_exact for native and interpreter runs (not part of any theorem).
 * The law draws the kind and the address (two u32 each), the two capacities (u32), the prior bytes of the header
 * scratch and of both arenas (nondet_bytes), then, per copy, whether it fails (u8) and the bytes (nondet_bytes),
 * and two u32 per answer of the adversarial Lean.  Uniform values would stop every run at the root selection.  So
 * this plan builds, per run, a firmware that holds a well-formed RSDT or XSDT and the tables it lists (mostly
 * one MADT, valid checksums, capacities that fit) and answers what an accepting Lean would, reading the law's
 * model (harness/table_copy_exact.h) for the chunk, the cursor and the step it is at.  Each run then perturbs
 * one place, with the values next to each check's boundary: the selection, the root's length, signature,
 * checksum or entries, one table's length, signature or checksum, the header against the copy, a capacity, a
 * failing copy, one stream transition or one sequence step.  A few runs carry a root of 255 to 257 entries or a
 * table of 64 KiB; under the interpreter (GP_RUNS defined), whose budget per seed they exceed, only roots of 257
 * entries, rejected before their entries are decoded. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"
#include "../harness/table_copy_exact.h"

extern uint64_t quickproof_rnd(void);

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

enum { ENV_NONE, ENV_SELECTION, ENV_ROOT, ENV_ENTRY, ENV_TABLE, ENV_HEADER, ENV_CAPACITY, ENV_FAIL, ENV_STREAM,
       ENV_SEQUENCE, ENV_TARGETS };
#define ENV_MAX 260u

static int env_planned, env_target, env_pick;
static unsigned long env_u32_calls, env_bytes_calls, env_copies, env_transitions, env_steps;
static uint64_t env_pending_lo;
static int env_have_lo;
static uint64_t env_kind, env_address, env_seed;
static uint32_t env_count, env_width, env_root_length, env_root_capacity, env_table_capacity;
static uint32_t env_length[ENV_MAX];
static uint64_t env_entry[ENV_MAX];
static int env_madt, env_madt2, env_bad_sum, env_bad_field, env_byte6, env_byte7;   /* -1: the root, t: table t */
static int env_bad_sig, env_header_lie;
static long env_fail_copy, env_stream_at, env_step_at, env_random_at, env_answers;
static int env_stream_word, env_step_word;
static uint64_t env_stream_value;
static int env_value_kind;
/* The SDT the firmware is copying: index (0 the root, t + 1 table t), its declared length, signature, checksum. */
static uint32_t env_sdt, env_declared;
static uint8_t env_sig[4], env_sum;

static uint32_t env_pad(uint32_t n) { return (n + 7) / 8 * 8; }

static uint8_t env_filler(uint32_t sdt, uint32_t i) {
    uint64_t x = env_seed + (uint64_t)sdt * 0x9e3779b97f4a7c15u + (uint64_t)i * 0xbf58476d1ce4e5b9u;
    x ^= x >> 29;
    x *= 0x94d049bb133111ebu;
    x ^= x >> 32;
    return (uint8_t)x;
}

static void env_plan(void) {
    env_planned = 1;
    env_seed = quickproof_rnd();
    static const int targets[20] = {ENV_NONE, ENV_NONE, ENV_NONE, ENV_SELECTION, ENV_ROOT, ENV_ROOT, ENV_ENTRY,
                                    ENV_ENTRY, ENV_TABLE, ENV_TABLE, ENV_TABLE, ENV_HEADER, ENV_CAPACITY,
                                    ENV_CAPACITY, ENV_FAIL, ENV_STREAM, ENV_STREAM, ENV_STREAM, ENV_STREAM,
                                    ENV_SEQUENCE};
    env_target = targets[env_r(20)];
    env_pick = (int)env_r(16);
    env_kind = 1 + env_r(2);
    env_address = 0x000e0000u + 16 * env_r(4096);
    if (env_r(16) == 0) env_address = 0xffffffffu;
    env_width = env_kind == 1 ? 4 : 8;
    /* Mostly one to four tables; sometimes none, five to eight, or a root at its 256-entry bound. */
    unsigned k = (unsigned)env_r(40);
    env_count = k < 2 ? 0 : k < 34 ? 1 + (uint32_t)env_r(4) : k < 38 ? 5 + (uint32_t)env_r(4) : 255 + (uint32_t)env_r(3);
#ifdef GP_RUNS
    /* The interpreter decodes 255 or 256 entries, and compares every pair, too slowly for its budget per seed:
       there a large root has 257 entries, which the pipeline rejects before decoding them. */
    if (env_count > 8) env_count = 257;
#endif
    int big_root = env_count > 8;
    /* A table of 64 KiB, mostly with nothing else perturbed; natively only, for the interpreter's budget. */
    int big_table = !big_root && env_r(12) == 0;
#ifdef GP_RUNS
    big_table = 0;
#endif
    if (big_table && env_r(2)) env_target = ENV_NONE;
    for (uint32_t t = 0; t < env_count && t < ENV_MAX; ++t) {
        env_length[t] = env_r(5) == 0 ? 36 : 37 + (uint32_t)env_r(env_r(4) == 0 ? 400 : 60);
        if (env_r(4) == 0) env_length[t] = env_pad(env_length[t]);
        env_entry[t] = 0x00100000u + 0x1000u * t + 16 * env_r(200);
    }
    if (big_table) env_length[env_r(env_count ? env_count : 1)] = 65536 - 8 * (uint32_t)env_r(2);
    env_root_length = 36 + env_count * env_width;
    env_madt = env_count ? (int)env_r(env_count) : -1;
    env_madt2 = -1;
    env_bad_sum = env_bad_field = env_byte6 = env_byte7 = env_bad_sig = env_header_lie = -2;
    env_fail_copy = env_stream_at = env_step_at = -1;
    env_random_at = env_r(10) == 0 ? (long)env_r(200) : -1;   /* one answer of any value */
    if (env_count && env_r(8) == 0) env_length[env_madt] = 36;   /* an MADT that is only a header */
    switch (env_target) {
    case ENV_SELECTION: {
        static const uint64_t kinds[4] = {0, 3, 0x100000001u, 0xffffffffffffffffu};
        static const uint64_t addresses[4] = {0, 0x100000000u, 0x1000000000u, 0xffffffffffffffffu};
        if (env_pick < 8) env_kind = kinds[env_pick % 4];
        else env_address = addresses[env_pick % 4];
        break;
    }
    case ENV_ROOT:   /* the root's width, signature, checksum or 64-KiB bound */
        if (env_pick < 4) env_root_length += 1 + (uint32_t)env_r(env_width - 1);
        else if (env_pick < 7) env_bad_sig = -1;
        else if (env_pick < 10) env_bad_sum = -1;
        else if (env_pick < 11) env_bad_field = -1;
        else if (env_pick < 12) env_byte6 = -1;
        else if (env_pick < 13) env_byte7 = -1;
        else env_root_length = 36;   /* no entries */
        if (env_root_length == 36) env_count = 0;
        break;
    case ENV_ENTRY:  /* one entry 0, 2^32 or more, 0xffffffff, or equal to an earlier one */
        if (env_count) {
            uint32_t at = (uint32_t)env_r(env_count);
            if (env_pick < 3) env_entry[at] = 0;
            else if (env_pick < 6) env_entry[at] = env_width == 8 ? 0x100000000u + env_r(4) : 0;
            else if (env_pick < 10) env_entry[at] = 0xffffffffu;
            else if (at > 0) env_entry[at] = env_entry[env_pick < 13 ? 0 : env_r(at)];
            else env_entry[at] = 1;
        }
        break;
    case ENV_TABLE:  /* one table's length, signature or checksum */
        if (env_count) {
            int at = (int)env_r(env_count);
            if (env_pick < 3) env_length[at] = (uint32_t[]){0, 35, 65537}[env_pick];
            else if (env_pick < 5) env_madt = -1;
            else if (env_pick < 8) env_madt2 = at;
            else if (env_pick < 11) env_bad_sum = at;
            else if (env_pick < 12) env_bad_field = at;
            else if (env_pick < 13) env_byte6 = at;
            else if (env_pick < 14) env_byte7 = at;
            else env_length[at] = env_pad(env_length[at]) + 8 * (uint32_t)env_r(3);
        }
        break;
    default:
        break;
    }
    if (env_count > ENV_MAX) env_count = ENV_MAX;
    /* Capacities that fit, with some slack; ENV_CAPACITY puts one at a boundary. */
    uint32_t total = 0;
    for (uint32_t t = 0; t < env_count; ++t) total += env_pad(env_length[t]);
    env_root_capacity = env_root_length + (env_r(3) == 0 ? 0 : (uint32_t)env_r(24));
    env_table_capacity = total + (env_r(3) == 0 ? 0 : (uint32_t)env_r(24));
    if (big_root) env_table_capacity = env_pad(env_length[0]) * (1 + (uint32_t)env_r(3));
    if (env_target == ENV_CAPACITY) {
        uint32_t at = env_count ? (uint32_t)env_r(env_count) : 0, before = 0;
        for (uint32_t t = 0; t < at; ++t) before += env_pad(env_length[t]);
        switch (env_count ? env_pick % 8 : env_pick % 2 ? 0 : 7) {
        case 0: env_root_capacity = env_root_length - 1; break;
        case 1:   /* past the 64-KiB cap; natively only, for the interpreter's budget */
#ifndef GP_RUNS
            env_root_capacity = 70000;
            env_root_length = 65537;
            break;
#endif
            env_root_capacity = env_root_length;
            break;
        case 2: env_table_capacity = before; break;                          /* full before table `at` */
        case 3: env_table_capacity = before + env_length[at]; break;          /* fits unpadded only */
        case 4: env_table_capacity = before + env_length[at] - 1; break;      /* does not fit */
        case 5: env_table_capacity = total; break;                            /* exact */
        case 6: env_table_capacity = 0; break;
        default: env_root_capacity = env_root_length; break;
        }
    }
    if (env_target == ENV_HEADER)   /* the header of the root or of one table differs from its copy */
        env_header_lie = env_count && env_pick % 2 ? (int)env_r(env_count) : -1;
    if (env_target == ENV_FAIL) env_fail_copy = (long)env_r(2 + 2 * (env_count < 4 ? env_count : 4));
    if (env_target == ENV_STREAM) {
        /* A transition: mostly the last of an SDT, where the cursor is checked hardest. */
        uint32_t chunks = (env_root_length + 7) / 8, sdt = (uint32_t)env_r(env_count + 1);
        uint32_t first = 0;
        for (uint32_t s = 0; s < sdt; ++s) first += (s == 0 ? env_root_length + 7 : env_length[s - 1] + 7) / 8;
        chunks = (sdt == 0 ? env_root_length + 7 : env_length[sdt - 1] + 7) / 8;
        env_stream_at = (long)first + (env_r(2) ? (long)chunks - 1 : (long)env_r(chunks ? chunks : 1));
        static const int words[5] = {1, 2, 4, 5, 6};
        env_stream_word = words[env_r(5)];
        env_value_kind = (int)env_r(8);
        env_stream_value = env_r(256);
    }
    if (env_target == ENV_SEQUENCE) {
        env_step_at = (long)env_r(env_count ? env_count : 1);
        env_step_word = 1 + (int)env_r(3);
        env_value_kind = (int)env_r(4);
    }
}

/* The accepting answer to the stream query the law is at, and the perturbed one at env_stream_at. */
static uint64_t env_stream_answer(void) {
    struct law *m = &law;
    if (m->word == 0) ++env_transitions;
    uint64_t end = m->length - m->byte < 8 ? m->length : m->byte + 8;
    uint64_t last = end == m->length;
    uint64_t chunk = 0;
    for (uint64_t i = m->byte; i < end; ++i) chunk |= (uint64_t)m->destination_expect[i] << (8 * (i - m->byte));
    static const int words[5] = {1, 2, 4, 5, 6};
    int word = words[m->word < 5 ? m->word : 0];
    uint64_t v = word == 1 ? 1 : word == 2 ? 0 : word == 4 ? end : word == 5 ?
                 (last ? m->cursor + env_pad(m->length) : m->cursor) : chunk;
    if ((long)env_transitions - 1 != env_stream_at || word != env_stream_word) return v;
    switch (word) {
    case 1: return (uint64_t[]){0, 2, 3, 0x100000001u, 0, 2, 1, 0xffffffffffffffffu}[env_value_kind];
    case 2: return (uint64_t[]){42, 43, 44, 45, 46, 47, 48, 1}[env_value_kind];
    case 4: return (uint64_t[]){end + 1, end - 1, end + 8, 0, end + 1, m->byte, end - 1, m->length}[env_value_kind];
    case 5: {
        uint64_t c = m->cursor, p = env_pad(m->length);
        if (!last) return (uint64_t[]){c + 1, c - 1, c + 8, 0, c + p, c + 1, c - 1, 0xffffffffffffffffu}[env_value_kind];
        return (uint64_t[]){c, c - 1, c + p + 1, c + p - 1, c + p + 0x100000000u, c + 1, c + p + 8, 0}[env_value_kind];
    }
    default: {
        uint64_t width = 8 * (end - m->byte);
        uint64_t beyond = width < 64 ? (uint64_t)1 << width : 0;
        return (uint64_t[]){chunk ^ 1, chunk ^ 0x8000000000000000u, chunk | beyond, chunk ^ 0x100, chunk + 1,
                            chunk ^ (env_stream_value << 8), 0, chunk ^ 0xff00000000000000u}[env_value_kind];
    }
    }
}

static uint64_t env_sequence_answer(void) {
    struct law *m = &law;
    if (m->word == 0) ++env_steps;
    uint64_t v = m->word == 0 ? 1 : m->word == 1 ? 0 : m->table + 1;
    if ((long)env_steps - 1 != env_step_at || (int)m->word + 1 != env_step_word) return v;
    if (m->word == 0) return (uint64_t[]){0, 2, 3, 0xffffffffffffffffu}[env_value_kind];
    if (m->word == 1) return (uint64_t[]){1, 48, 49, 0xffffffffffffffffu}[env_value_kind];
    return (uint64_t[]){m->table, m->table + 2, 0, m->count + 1}[env_value_kind];
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    unsigned long k = env_u32_calls++;
    if (k < 6) {   /* kind and address (high word first), the root and table capacities */
        uint64_t v = k < 2 ? env_kind : k < 4 ? env_address : k == 4 ? env_root_capacity : env_table_capacity;
        return (uint32_t)(k == 0 || k == 2 ? v >> 32 : v);
    }
    if (env_have_lo) {
        env_have_lo = 0;
        return (uint32_t)env_pending_lo;
    }
    uint64_t v = law.expect == EXPECT_STREAM ? env_stream_answer() :
                 law.expect == EXPECT_SEQUENCE ? env_sequence_answer() : quickproof_rnd();
    if ((long)env_answers++ == env_random_at) v = quickproof_rnd();
    env_pending_lo = v & 0xffffffffu;
    env_have_lo = 1;
    return (uint32_t)(v >> 32);
}

uint8_t nondet_u8(void) {   /* a copy fails only where planned */
    if (!env_planned) env_plan();
    long k = (long)env_copies++;
    return (uint8_t)(k == env_fail_copy ? 0 : 1 + env_r(255));
}

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

/* SDT s's byte i as the firmware holds it: `body` 0 for the header copy, 1 for the full copy. */
static uint8_t env_sdt_byte(uint32_t s, uint32_t i, int body) {
    if (i < 4) return env_sig[i];
    if (i < 8) {
        uint32_t field = env_declared;
        int at = (int)s - 1;
        if (body && env_bad_field == at) field = env_declared + 1;
        if (body && env_byte6 == at) field |= (uint32_t)(1 + env_filler(s, 6) % 255) << 16;
        if (body && env_byte7 == at) field |= 0x80000000u;
        return (uint8_t)(field >> (8 * (i - 4)));
    }
    if (i == 9) return env_sum;
    if (s == 0 && i >= 36 && i < 36 + env_count * env_width) {
        uint32_t e = (i - 36) / env_width, b = (i - 36) % env_width;
        return (uint8_t)(env_entry[e] >> (8 * b));
    }
    return env_filler(s, i);
}

/* A new SDT: its signature, declared length and checksum. */
static void env_begin_sdt(void) {
    struct law *m = &law;
    env_sdt = m->is_root ? 0 : m->table + 1;
    int at = (int)env_sdt - 1;
    const char *sig = m->is_root ? (env_kind == 1 ? "RSDT" : "XSDT") : (at == env_madt || at == env_madt2) ?
                      "APIC" : (const char *[]){"FACP", "HPET", "MCFG", "WAET"}[at % 4];
    for (int i = 0; i < 4; ++i) env_sig[i] = (uint8_t)sig[i];
    if (env_bad_sig == at) env_sig[1 + env_r(3)] ^= 0x20;
    env_declared = m->is_root ? env_root_length : at < (int)ENV_MAX ? env_length[at] : 36;
    env_sum = 0;
    uint32_t sum = 0;
    for (uint32_t i = 0; i < env_declared && i < 65536; ++i) sum += env_sdt_byte(env_sdt, i, 1);
    env_sum = (uint8_t)(0 - sum);
    if (env_bad_sum == at) env_sum = (uint8_t)(env_sum + 1 + env_r(255));
}

void nondet_bytes(uint8_t *buf, size_t n) {
    if (!env_planned) env_plan();
    unsigned long k = env_bytes_calls++;
    if (k < 3) {   /* the prior bytes of the header scratch and of the arenas: never 0 */
        for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)(1 + env_r(255));
        return;
    }
    if (law.expect == EXPECT_HEADER) env_begin_sdt();
    int body = law.expect == EXPECT_BODY;
    for (size_t i = 0; i < n; ++i) buf[i] = env_sdt_byte(env_sdt, (uint32_t)i, body);
    int at = (int)env_sdt - 1;
    if (env_header_lie == at) {
        if (body && env_pick % 4 < 2)   /* one byte of the copy is not the header's */
            buf[env_r(n)] ^= (uint8_t)(1 + env_r(255));
        if (!body && env_pick % 4 >= 2) {   /* the header declares another length than the copy */
            uint32_t declared = env_declared + (env_pick % 2 ? 1 : 8);
            for (int i = 0; i < 4; ++i) buf[4 + i] = (uint8_t)(declared >> (8 * i));
        }
    }
    if (!body && env_byte7 == at && env_r(2)) buf[7] |= 0x80;   /* a declared length of 2^31 or more */
}
