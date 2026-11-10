/* Value distributions of the law image_exact for native and interpreter runs (not part of any theorem).
 * The law draws the function to call (u8).  For the header and wifi_start it then draws the image's length
 * (u32) and bytes (nondet_bytes), then the prior values of the objects the function writes (u32 each, and for
 * wifi_start the scratch through nondet_bytes).  For an admission it draws two targets and two policies, field
 * by field (u32 each; a 64-bit bitmap as two, high word first).
 *
 * Uniform bytes would almost never make an image the parser accepts, so each run draws one of the scenarios
 * below (each one check's boundary) and builds for it a well-formed image in the format of
 * Bytecode.Program.image: version 1, 2 or 3; a version 3 image with 0 to 8 sinks and no, an empty or a 1 to 16
 * entry descriptor map; then code and a blob whose sizes fit, or none (a minimal image, whose length is exactly
 * its header's).  The scenario then changes the image next to its check: a length one byte short of or exactly
 * at each length check, a version 3 image cut to 32..67 bytes, the magic, the version, a stray BDF bit, BAR
 * offsets below, above, inside but unaligned, at the edges and with only the top byte set, windows at and next
 * to 0, 512 and 0x10000, the flags, the policy window next to the target's, 8 and 9 sinks, 16 and 17
 * descriptors, a descriptor's kind, count (0, 1, 4096, 4097) or limit (262144, one past it, a product past
 * 2^32), and the instruction count and blob length (one off, and a count one past the fit with a blob length
 * that wraps).  Size scenarios call wifi_start, the others the header or (one in three) wifi_start.
 *
 * An admission scenario starts from a policy pair that passes (p declares all of max's sinks and descriptors
 * and more, rotated, with a smaller window and DMA field and bitmaps inside max's) and a matching target, then
 * perturbs one field next to its check, puts the only copy of a needed sink or descriptor just past p's count,
 * puts one p lacks just past max's count, or changes nothing; a frame-source scenario starts from a target and
 * policy that pass and perturbs one field.  Under the interpreter (GP_RUNS defined), three in four wifi_start
 * calls become header calls and the prior scratch is a cheap pattern, since the law fills, copies and compares
 * the 256 KiB scratch. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"
#include "../harness/image_exact.h"

extern uint64_t quickproof_rnd(void);

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

#define ENV_IMAGE_MAX 1024u
#define ENV_QUEUE_MAX 256u

static int env_planned;
static uint32_t env_call, env_len;
static uint8_t env_image[ENV_IMAGE_MAX];
static uint32_t env_queue[ENV_QUEUE_MAX];
static unsigned env_qn, env_qi, env_bytes_calls;

static void env_push(uint32_t v) {
    if (env_qn < ENV_QUEUE_MAX)
        env_queue[env_qn++] = v;
}

static void env_put32(uint32_t at, uint32_t v) {
    if (at + 4 <= ENV_IMAGE_MAX) {
        env_image[at] = (uint8_t)v;
        env_image[at + 1] = (uint8_t)(v >> 8);
        env_image[at + 2] = (uint8_t)(v >> 16);
        env_image[at + 3] = (uint8_t)(v >> 24);
    }
}

static uint32_t env_get32(uint32_t at) {
    return (uint32_t)env_image[at] | (uint32_t)env_image[at + 1] << 8 | (uint32_t)env_image[at + 2] << 16 |
           (uint32_t)env_image[at + 3] << 24;
}

/* One of the n values. */
static uint32_t env_pick(const uint32_t *v, unsigned n) { return v[env_r(n)]; }

/* A value next to v: v itself, or v plus or minus one. */
static uint32_t env_near(uint32_t v) {
    unsigned k = (unsigned)env_r(3);
    return k == 0 ? v : k == 1 ? v + 1u : v - 1u;
}

/* ---- Images ---- */

/* The image scenarios. */
enum { I_VALID, I_MIN_V1, I_MIN_V2, I_MIN_V3, I_MIN_MAP, I_MIN_EMPTY_MAP, I_SHORT_SINKS, I_SHORT_COUNT,
       I_SHORT_MAP, I_SHORT_V3, I_SHORT_V3_LOW, I_SHORT_V2, I_SHORT_V1, I_RANDOM, I_MAGIC, I_VERSION, I_BDF,
       I_BAR_LOW, I_BAR_HIGH, I_BAR_UNALIGNED, I_BAR_EDGE, I_BAR_TOP, I_WINDOW_LOW, I_WINDOW_UNALIGNED,
       I_WINDOW_HIGH, I_FLAGS, I_POLICY_WINDOW, I_SINKS_8, I_SINKS_9, I_DESC_COUNT, I_DESC_KIND, I_DESC_ENTRIES,
       I_DESC_LIMIT, I_DESC_OVERFLOW, I_SIZES, I_SIZES_WRAP, I_START, I_COUNT };

/* The layout of the image being built. */
static uint32_t env_version, env_sinks, env_descs, env_map_at, env_header, env_n, env_blob;
static int env_has_map;

/* A descriptor inside the scratch: kind, start, count and stride with limit at most 262144. */
static void env_desc(uint32_t at) {
    uint32_t kind = (uint32_t)env_r(2);
    uint32_t count = env_r(4) == 0 ? 4096u - (uint32_t)env_r(2) : 1u + (uint32_t)env_r(64);
    uint32_t size = kind ? 16u : 8u;
    uint32_t stride = env_r(4) == 0 ? 0u : size * (1u + (uint32_t)env_r(4));
    uint64_t span = (uint64_t)stride * (count - 1u) + size;
    uint32_t start;
    if (span > 262144u) {   /* too wide: one entry */
        count = 1;
        start = (uint32_t)env_r(262144u - size + 1u);
    } else {
        start = (uint32_t)env_r(262144u - span + 1u);
    }
    env_put32(at, kind);
    env_put32(at + 4, start);
    env_put32(at + 8, count);
    env_put32(at + 12, stride);
}

/* A well-formed image (Bytecode.Program.image's layout).  version: 0 for any; map: -1 any, 0 none, 1 one to 16
   descriptors, 2 an empty map (flags bit 1, count 0); code: 0 none (minimal), 1 up to 8 words and a blob,
   2 15 to 24 words and a blob. */
static void env_build(uint32_t version, int map, int code) {
    if (version == 0) {
        unsigned v = (unsigned)env_r(10);
        version = v == 0 ? 1u : v < 3 ? 2u : 3u;
    }
    if (map != -1 && version != 3) map = -1;
    env_version = version;
    env_put32(0, 0x4649574cu);
    env_put32(4, version);
    env_header = 16;
    env_sinks = 0;
    env_descs = 0;
    env_has_map = 0;
    env_map_at = 0;
    if (version >= 2) {
        uint32_t bus = (uint32_t)env_r(256), dev = (uint32_t)env_r(32), fn = (uint32_t)env_r(8);
        uint32_t window = 512u * (env_r(8) == 0 ? 128u : 1u + (uint32_t)env_r(32));
        uint32_t bar = env_r(2) ? 0u : 0x10u + 4u * (uint32_t)env_r(6);
        env_put32(16, bus << 16 | dev << 8 | fn);
        env_put32(20, (uint32_t)quickproof_rnd());
        env_put32(24, window);
        env_put32(28, bar);
        env_header = 32;
        if (version == 3) {
            if (map == -1) map = (int)env_r(3);
            env_has_map = map != 0;
            env_put32(32, (uint32_t)env_r(2) | (env_has_map ? 2u : 0u));
            env_put32(36, window + 512u * (uint32_t)env_r(3));
            for (uint32_t at = 40; at < 64; at += 4)
                env_put32(at, env_r(4) == 0 ? 0u : (uint32_t)quickproof_rnd());
            env_sinks = (uint32_t)env_r(9);
            env_put32(64, env_sinks);
            for (uint32_t i = 0; i < env_sinks; ++i)
                env_put32(68 + 4 * i, 8u * (uint32_t)env_r(1024));
            env_header = 68 + 4 * env_sinks;
            if (env_has_map) {
                env_map_at = env_header;
                env_descs = map == 2 ? 0u : env_r(4) == 0 ? 16u : 1u + (uint32_t)env_r(16);
                env_put32(env_map_at, env_descs);
                for (uint32_t i = 0; i < env_descs; ++i)
                    env_desc(env_map_at + 4 + 16 * i);
                env_header = env_map_at + 4 + 16 * env_descs;
            }
        }
    }
    env_n = code == 0 ? 0u : code == 1 ? (uint32_t)env_r(9) : 15u + (uint32_t)env_r(10);
    env_blob = code == 0 ? 0u : (uint32_t)env_r(33);
    env_put32(8, env_n);
    env_put32(12, env_blob);
    env_len = env_header + 16 * env_n + env_blob;
    for (uint32_t i = env_header; i < env_len; ++i)
        env_image[i] = (uint8_t)quickproof_rnd();
}

/* The index of a random descriptor's first word, or 0 when there is none. */
static uint32_t env_some_desc(void) {
    return env_descs ? env_map_at + 4 + 16 * (uint32_t)env_r(env_descs) : 0u;
}

/* Build the scenario's image; return 1 when it is a size scenario (wifi_start only). */
static int env_image_case(unsigned c) {
    switch (c) {
    case I_MIN_V1: env_build(1, -1, 0); break;
    case I_MIN_V2: env_build(2, -1, 0); break;
    case I_MIN_V3: env_build(3, 0, 0); break;
    case I_MIN_MAP: env_build(3, 1, 0); break;
    case I_MIN_EMPTY_MAP: env_build(3, 2, 0); break;
    case I_SHORT_SINKS: env_build(3, 0, 0); env_len = 68 + 4 * env_sinks - 1u; break;
    case I_SHORT_COUNT: env_build(3, 1 + (int)env_r(2), 0); env_len = env_map_at + 4u - 1u - (uint32_t)env_r(4); break;
    case I_SHORT_MAP: env_build(3, 1, 0); env_len = env_header - 1u - (uint32_t)env_r(16); break;
    case I_SHORT_V3: env_build(3, -1, 1); env_len = 64u + (uint32_t)env_r(4); break;
    case I_SHORT_V3_LOW: env_build(3, -1, 1); env_len = 32u + (uint32_t)env_r(32); break;
    case I_SHORT_V2: env_build(2, -1, 1); env_len = env_r(2) ? 31u : 16u + (uint32_t)env_r(16); break;
    case I_SHORT_V1: env_build(1, -1, 1); env_len = env_r(2) ? 15u + (uint32_t)env_r(2) : (uint32_t)env_r(17); break;
    case I_RANDOM:
        env_len = (uint32_t)env_r(128);
        for (uint32_t i = 0; i < env_len; ++i)
            env_image[i] = (uint8_t)quickproof_rnd();
        if (env_r(2)) env_put32(0, 0x4649574cu);
        if (env_r(2)) env_put32(4, 1u + (uint32_t)env_r(3));
        break;
    case I_MAGIC: env_build(0, -1, 1); env_image[env_r(4)] ^= (uint8_t)(1u << env_r(8)); break;
    case I_VERSION: {
        static const uint32_t v[6] = {0, 4, 5, 0xffffffffu, 0x80000003u, 0x103u};
        env_build(0, -1, 1);
        env_put32(4, env_pick(v, 6));
        break;
    }
    case I_BDF: {
        static const uint32_t bits[16] = {3, 4, 5, 6, 7, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31};
        env_build(2 + (uint32_t)env_r(2), -1, 1);
        env_put32(16, env_get32(16) ^ (1u << env_pick(bits, 16)));
        break;
    }
    case I_BAR_LOW: {
        static const uint32_t v[4] = {0x0c, 0x0f, 0x04, 0x01};
        env_build(2 + (uint32_t)env_r(2), -1, 1);
        env_put32(28, env_pick(v, 4));
        break;
    }
    case I_BAR_HIGH: {
        static const uint32_t v[4] = {0x28, 0x25, 0x26, 0x2c};
        env_build(2 + (uint32_t)env_r(2), -1, 1);
        env_put32(28, env_pick(v, 4));
        break;
    }
    case I_BAR_UNALIGNED: {
        static const uint32_t v[5] = {0x11, 0x12, 0x13, 0x22, 0x23};
        env_build(2 + (uint32_t)env_r(2), -1, 1);
        env_put32(28, env_pick(v, 5));
        break;
    }
    case I_BAR_EDGE: {
        static const uint32_t v[3] = {0x10, 0x24, 0x14};
        env_build(2 + (uint32_t)env_r(2), -1, 1);
        env_put32(28, env_pick(v, 3));
        break;
    }
    case I_BAR_TOP: {
        static const uint32_t v[4] = {0x01000000u, 0x80000000u, 0x01000010u, 0x00000110u};
        env_build(2 + (uint32_t)env_r(2), -1, 1);
        env_put32(28, env_pick(v, 4));
        break;
    }
    case I_WINDOW_LOW: {
        static const uint32_t v[4] = {0, 1, 511, 512};
        env_build(2, -1, 1);
        env_put32(24, env_pick(v, 4));
        break;
    }
    case I_WINDOW_UNALIGNED: {
        static const uint32_t v[4] = {513, 0x8100, 0x1ff00, 0x300};
        env_build(2, -1, 1);
        env_put32(24, env_pick(v, 4));
        break;
    }
    case I_WINDOW_HIGH: {
        static const uint32_t v[4] = {0x10000, 0x10200, 0x10001, 0xfe00};
        env_build(2 + (uint32_t)env_r(2), -1, 1);
        env_put32(24, env_pick(v, 4));
        if (env_version == 3) env_put32(36, 0x10200u);
        break;
    }
    case I_FLAGS: {
        static const uint32_t v[6] = {3, 4, 5, 6, 0x80000000u, 0x80000001u};
        env_build(3, -1, 1);
        env_put32(32, env_pick(v, 6));
        break;
    }
    case I_POLICY_WINDOW: env_build(3, -1, 1); env_put32(36, env_near(env_get32(24))); break;
    case I_SINKS_8:
        env_build(3, 0, (int)env_r(2));
        /* Rebuild the sink table with 8 entries and no code. */
        env_sinks = 8;
        env_put32(64, 8);
        for (uint32_t i = 0; i < 8; ++i) env_put32(68 + 4 * i, 8u * (uint32_t)env_r(1024));
        env_header = 100;
        env_put32(8, 0);
        env_put32(12, 0);
        env_len = 100;
        break;
    case I_SINKS_9: {
        static const uint32_t v[4] = {9, 10, 0x40000001u, 0xffffffffu};
        env_build(3, 0, 0);
        env_put32(64, env_pick(v, 4));
        env_len = 68 + 4 * 9 + (uint32_t)env_r(16);
        break;
    }
    case I_DESC_COUNT: {
        static const uint32_t v[4] = {17, 18, 0x10000001u, 0xffffffffu};
        env_build(3, 1, 1);
        env_put32(env_map_at, env_pick(v, 4));
        env_len = env_map_at + 4 + 16 * 17 + (uint32_t)env_r(16);
        if (env_len > ENV_IMAGE_MAX) env_len = ENV_IMAGE_MAX;
        break;
    }
    case I_DESC_KIND: {
        static const uint32_t v[3] = {2, 3, 0xffffffffu};
        env_build(3, 1, 1);
        env_put32(env_some_desc(), env_pick(v, 3));
        break;
    }
    case I_DESC_ENTRIES: {
        static const uint32_t v[4] = {0, 4097, 4096, 1};
        env_build(3, 1, 1);
        uint32_t e = env_some_desc();
        env_put32(e + 4, 0);
        env_put32(e + 8, env_pick(v, 4));
        env_put32(e + 12, env_r(2) ? 0u : 16u);
        break;
    }
    case I_DESC_LIMIT: {
        /* A region whose limit is 262144 exactly, or one past it. */
        env_build(3, 1, 1);
        uint32_t e = env_some_desc();
        uint32_t size = (env_get32(e) & 1u) ? 16u : 8u;
        uint32_t count = 1u + (uint32_t)env_r(8), stride = size * (uint32_t)env_r(4);
        uint32_t span = stride * (count - 1u) + size;
        env_put32(e + 4, 262144u - span + (uint32_t)env_r(2));
        env_put32(e + 8, count);
        env_put32(e + 12, stride);
        break;
    }
    case I_DESC_OVERFLOW: {
        /* stride * (count - 1) past 2^32, or start + span past 2^32. */
        env_build(3, 1, 1);
        uint32_t e = env_some_desc();
        if (env_r(2)) {
            env_put32(e + 4, 0);
            env_put32(e + 8, 4096);
            env_put32(e + 12, 0x00100000u + (uint32_t)env_r(2));
        } else {
            env_put32(e + 4, 0xfffffff8u + (uint32_t)env_r(8));
            env_put32(e + 8, 1);
        }
        break;
    }
    case I_SIZES: {
        env_build(0, -1, 1);
        unsigned k = (unsigned)env_r(4);
        if (k == 0) env_put32(8, env_n + 1u);
        else if (k == 1) env_put32(8, env_n - 1u);
        else env_put32(12, env_r(2) ? env_blob + 1u : env_blob - 1u);
        return 1;
    }
    case I_SIZES_WRAP: {
        /* One instruction more than fits, with the blob length that 16N wraps to. */
        env_build(0, -1, 2);
        uint32_t room = env_len - env_header;
        uint32_t n = room / 16 + (uint32_t)env_r(2);
        env_put32(8, n);
        env_put32(12, room - 16u * n);
        if (env_r(4) == 0) env_put32(8, 0x10000000u + (uint32_t)env_r(2));
        return 1;
    }
    case I_START: env_build(0, -1, 1); return 1;
    default: env_build(0, -1, 1); break;
    }
    return 0;
}

/* ---- Policies and targets for the admission ---- */

static struct wifi_target env_t, env_want;
static struct wifi_policy env_p, env_max;

static void env_random_policy(struct wifi_policy *p) {
    p->present = (uint32_t)quickproof_rnd();
    p->dma = (uint32_t)quickproof_rnd();
    p->window = (uint32_t)quickproof_rnd();
    p->cfg_read = quickproof_rnd();
    p->cfg_write = quickproof_rnd();
    p->cmd_clear = (uint32_t)quickproof_rnd();
    p->cmd_set = (uint32_t)quickproof_rnd();
    p->sink_count = (uint32_t)env_r(WIFI_MAX_SINKS + 1);
    for (uint32_t i = 0; i < WIFI_MAX_SINKS; ++i)
        p->sinks[i] = 8u * (uint32_t)env_r(512);
    p->desc_count = (uint32_t)env_r(WIFI_MAX_DESCS + 1);
    for (uint32_t i = 0; i < WIFI_MAX_DESCS; ++i) {
        p->descs[i].trb = (uint32_t)env_r(2);
        p->descs[i].start = 16u * (uint32_t)env_r(4096);
        p->descs[i].count = 1u + (uint32_t)env_r(64);
        p->descs[i].stride = 16u * (uint32_t)env_r(4);
    }
}

/* max with at least one sink and one descriptor when `need`; p a policy within it. */
static void env_pair(int need) {
    struct wifi_policy *p = &env_p, *max = &env_max;
    env_random_policy(max);
    max->window = 512u * (uint32_t)env_r(64);
    max->dma = (uint32_t)env_r(3);
    if (need) {
        if (max->sink_count == 0) max->sink_count = 1u + (uint32_t)env_r(WIFI_MAX_SINKS);
        if (max->desc_count == 0) max->desc_count = 1u + (uint32_t)env_r(WIFI_MAX_DESCS);
    }
    env_random_policy(p);
    p->present = 1u + (uint32_t)env_r(4);
    p->dma = env_r(2) ? max->dma : 0u;
    p->window = max->window >= 1024u && env_r(2) ? max->window - 512u : max->window;
    p->cfg_read = max->cfg_read & quickproof_rnd();
    p->cfg_write = max->cfg_write & quickproof_rnd();
    p->cmd_clear = max->cmd_clear & (uint32_t)quickproof_rnd();
    p->cmd_set = max->cmd_set & (uint32_t)quickproof_rnd();
    p->sink_count = max->sink_count + (uint32_t)env_r(WIFI_MAX_SINKS - max->sink_count + 1);
    uint32_t rot = (uint32_t)env_r(WIFI_MAX_SINKS);
    for (uint32_t i = 0; i < p->sink_count; ++i)
        p->sinks[(i + rot) % p->sink_count] = i < max->sink_count ? max->sinks[i] : 4u + 8u * (uint32_t)env_r(512);
    p->desc_count = max->desc_count + (uint32_t)env_r(WIFI_MAX_DESCS - max->desc_count + 1);
    rot = (uint32_t)env_r(WIFI_MAX_DESCS);
    for (uint32_t i = 0; i < p->desc_count; ++i) {
        uint32_t at = (i + rot) % p->desc_count;
        if (i < max->desc_count) p->descs[at] = max->descs[i];
        else p->descs[at].start = 8u + 16u * (uint32_t)env_r(4096);
    }
    env_t.bus = (uint32_t)env_r(256);
    env_t.dev = (uint32_t)env_r(32);
    env_t.fn = (uint32_t)env_r(8);
    env_t.id = (uint32_t)quickproof_rnd();
    env_t.window = max->window;
    env_t.bar = 0x10u + 4u * (uint32_t)env_r(6);
    env_want = env_t;
}

static uint64_t env_bit_outside(uint64_t mask, unsigned lo, unsigned width) {
    for (int tries = 0; tries < 64; ++tries) {
        uint64_t b = (uint64_t)1 << (lo + env_r(width));
        if (!(mask & b)) return b;
    }
    return (uint64_t)1 << lo;
}

/* The index in p of a copy of max's sink s (8 if none). */
static uint32_t env_find_sink(uint32_t s) {
    for (uint32_t i = 0; i < env_p.sink_count; ++i)
        if (env_p.sinks[i] == s) return i;
    return WIFI_MAX_SINKS;
}

static int env_same_desc(const struct wifi_desc *a, const struct wifi_desc *b) {
    return a->trb == b->trb && a->start == b->start && a->count == b->count && a->stride == b->stride;
}

/* The admission scenarios: within and the device service. */
enum { A_NONE, A_NONE2, A_SINK, A_DESC_TRB, A_DESC_START, A_DESC_COUNT, A_DESC_STRIDE, A_WINDOW, A_DMA, A_DMA_ZERO,
       A_CFG_READ_LO, A_CFG_READ_HI, A_CFG_WRITE_LO, A_CFG_WRITE_HI, A_CMD_CLEAR, A_CMD_SET, A_PRESENT, A_T_BUS,
       A_T_DEV, A_T_FN, A_T_ID, A_T_WINDOW, A_T_BAR, A_PAST_P_SINK, A_PAST_P_DESC, A_PAST_MAX_SINK,
       A_PAST_MAX_DESC, A_COUNT };

static void env_admission_case(unsigned c) {
    struct wifi_policy *p = &env_p, *max = &env_max;
    env_pair((c >= A_SINK && c <= A_DESC_STRIDE) || c >= A_PAST_P_SINK);
    env_call = c >= A_PRESENT && c <= A_T_BAR ? CALL_SERVICE : env_r(2) ? CALL_SERVICE : CALL_WITHIN;
    switch (c) {
    case A_SINK: {
        uint32_t s = max->sinks[env_r(max->sink_count)];
        for (uint32_t i = 0; i < p->sink_count; ++i)
            if (p->sinks[i] == s) p->sinks[i] = s ^ (1u << env_r(32));
        break;
    }
    case A_DESC_TRB: case A_DESC_START: case A_DESC_COUNT: case A_DESC_STRIDE: {
        struct wifi_desc d = max->descs[env_r(max->desc_count)];
        for (uint32_t i = 0; i < p->desc_count; ++i)
            if (env_same_desc(&p->descs[i], &d)) {
                if (c == A_DESC_TRB) p->descs[i].trb ^= 1u << env_r(32);
                else if (c == A_DESC_START) p->descs[i].start += env_r(2) ? 1u : 0xffffffffu;
                else if (c == A_DESC_COUNT) p->descs[i].count += env_r(2) ? 1u : 0xffffffffu;
                else p->descs[i].stride += env_r(2) ? 1u : 0xffffffffu;
            }
        break;
    }
    case A_WINDOW: p->window = env_near(max->window); break;
    case A_DMA: p->dma = env_near(max->dma); break;
    case A_DMA_ZERO: max->dma = 0; p->dma = (uint32_t)env_r(2) << env_r(32); break;
    case A_CFG_READ_LO: p->cfg_read |= env_bit_outside(max->cfg_read, 0, 32); break;
    case A_CFG_READ_HI: p->cfg_read |= env_bit_outside(max->cfg_read, 32, 32); break;
    case A_CFG_WRITE_LO: p->cfg_write |= env_bit_outside(max->cfg_write, 0, 32); break;
    case A_CFG_WRITE_HI: p->cfg_write |= env_bit_outside(max->cfg_write, 32, 32); break;
    case A_CMD_CLEAR: p->cmd_clear |= (uint32_t)env_bit_outside(max->cmd_clear, 0, 32); break;
    case A_CMD_SET: p->cmd_set |= (uint32_t)env_bit_outside(max->cmd_set, 0, 32); break;
    case A_PRESENT: p->present = 0; break;
    case A_T_BUS: env_t.bus += env_r(2) ? 1u : 0xffffffffu; break;
    case A_T_DEV: env_t.dev += env_r(2) ? 1u : 0xffffffffu; break;
    case A_T_FN: env_t.fn += env_r(2) ? 1u : 0xffffffffu; break;
    case A_T_ID: env_t.id += env_r(2) ? 1u : 0xffffffffu; break;
    case A_T_WINDOW: env_t.window += env_r(2) ? 1u : 0xffffffffu; break;
    case A_T_BAR: env_t.bar += env_r(2) ? 1u : 0xffffffffu; break;
    case A_PAST_P_SINK:
        /* The only copy of max's first sink sits just past p's count. */
        if (p->sink_count == WIFI_MAX_SINKS) p->sink_count--;
        for (uint32_t i; (i = env_find_sink(max->sinks[0])) < p->sink_count;)
            p->sinks[i] ^= 2u;
        p->sinks[p->sink_count] = max->sinks[0];
        break;
    case A_PAST_P_DESC:
        if (p->desc_count == WIFI_MAX_DESCS) p->desc_count--;
        for (uint32_t i = 0; i < p->desc_count; ++i)
            if (env_same_desc(&p->descs[i], &max->descs[0])) p->descs[i].start ^= 2u;
        p->descs[p->desc_count] = max->descs[0];
        break;
    case A_PAST_MAX_SINK:
        /* A sink p lacks sits just past max's count. */
        if (max->sink_count == WIFI_MAX_SINKS) max->sink_count--;
        max->sinks[max->sink_count] = 0xfffffff3u;
        break;
    case A_PAST_MAX_DESC:
        if (max->desc_count == WIFI_MAX_DESCS) max->desc_count--;
        max->descs[max->desc_count].start = 0xfffffff3u;
        break;
    default:
        break;
    }
}

/* The frame-source scenarios. */
enum { S_NONE, S_NONE2, S_BUS, S_DEV, S_FN, S_ID, S_TWINDOW, S_PRESENT, S_SINKS, S_DESCS, S_WINDOW, S_DMA,
       S_CFG_READ, S_CFG_WRITE, S_CMD_CLEAR, S_CMD_SET, S_COUNT };

static void env_source_case(unsigned c) {
    env_call = CALL_SOURCE;
    env_random_policy(&env_max);
    env_max.window = 512u * (1u + (uint32_t)env_r(8));
    env_random_policy(&env_p);
    env_p.present = 1u + (uint32_t)env_r(4);
    env_p.sink_count = 0;
    env_p.desc_count = 0;
    env_p.window = env_max.window - 512u * (uint32_t)env_r(2);
    env_p.dma = 0;
    env_p.cfg_read = 0;
    env_p.cfg_write = 0;
    env_p.cmd_clear = 0;
    env_p.cmd_set = 0;
    env_t.bus = 0;
    env_t.dev = 0;
    env_t.fn = 0;
    env_t.id = 0xffffffffu;
    env_t.window = env_max.window;
    env_t.bar = (uint32_t)quickproof_rnd();
    env_random_policy(&env_max);   /* only max's window is read: the rest stays random */
    env_max.window = env_t.window;
    switch (c) {
    case S_BUS: env_t.bus = 1u << env_r(32); break;
    case S_DEV: env_t.dev = 1u << env_r(32); break;
    case S_FN: env_t.fn = 1u << env_r(32); break;
    case S_ID: env_t.id = env_r(2) ? 0xfffffffeu : 0x7fffffffu; break;
    case S_TWINDOW: env_t.window = env_near(env_max.window); break;
    case S_PRESENT: env_p.present = 0; break;
    case S_SINKS: env_p.sink_count = 1u + (uint32_t)env_r(8); break;
    case S_DESCS: env_p.desc_count = 1u + (uint32_t)env_r(16); break;
    case S_WINDOW: env_p.window = env_near(env_max.window); break;
    case S_DMA: env_p.dma = 1u << env_r(32); break;
    case S_CFG_READ: env_p.cfg_read = (uint64_t)1 << env_r(64); break;
    case S_CFG_WRITE: env_p.cfg_write = (uint64_t)1 << env_r(64); break;
    case S_CMD_CLEAR: env_p.cmd_clear = 1u << env_r(32); break;
    case S_CMD_SET: env_p.cmd_set = 1u << env_r(32); break;
    default: break;
    }
}

static void env_push_target(const struct wifi_target *t) {
    env_push(t->bus);
    env_push(t->dev);
    env_push(t->fn);
    env_push(t->id);
    env_push(t->window);
    env_push(t->bar);
}

/* In the order of the law's any_policy. */
static void env_push_policy(const struct wifi_policy *p) {
    env_push(p->present);
    env_push(p->dma);
    env_push(p->window);
    env_push((uint32_t)(p->cfg_read >> 32));
    env_push((uint32_t)p->cfg_read);
    env_push((uint32_t)(p->cfg_write >> 32));
    env_push((uint32_t)p->cfg_write);
    env_push(p->cmd_clear);
    env_push(p->cmd_set);
    env_push(p->sink_count);
    for (uint32_t i = 0; i < WIFI_MAX_SINKS; ++i)
        env_push(p->sinks[i]);
    env_push(p->desc_count);
    for (uint32_t i = 0; i < WIFI_MAX_DESCS; ++i) {
        env_push(p->descs[i].trb);
        env_push(p->descs[i].start);
        env_push(p->descs[i].count);
        env_push(p->descs[i].stride);
    }
}

static void env_plan(void) {
    env_planned = 1;
    env_qn = 0;
    env_qi = 0;
    env_bytes_calls = 0;
    unsigned c = (unsigned)env_r(I_COUNT + A_COUNT + S_COUNT);
    if (c < I_COUNT) {
        int sizes = env_image_case(c);
        env_call = sizes || env_r(3) == 0 ? CALL_START : CALL_HEADER;
#ifdef GP_RUNS
        if (env_call == CALL_START && env_r(4) != 0)
            env_call = CALL_HEADER;
#endif
        if (env_len > ENV_IMAGE_MAX) env_len = ENV_IMAGE_MAX;
        env_push(env_len);
        return;
    }
    if (c < I_COUNT + A_COUNT)
        env_admission_case(c - I_COUNT);
    else
        env_source_case(c - I_COUNT - A_COUNT);
    env_push_target(&env_t);
    env_push_target(&env_want);
    env_push_policy(&env_p);
    env_push_policy(&env_max);
}

uint8_t nondet_u8(void) {
    if (!env_planned) env_plan();
    return (uint8_t)(env_call == CALL_SOURCE && env_r(2) ? 4 + env_r(252) : env_call);
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    if (env_qi < env_qn) return env_queue[env_qi++];
    return (uint32_t)quickproof_rnd();
}

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    if (!env_planned) env_plan();
    unsigned k = env_bytes_calls++;
    if (k == 0) {
        for (size_t i = 0; i < n; ++i)
            buf[i] = i < ENV_IMAGE_MAX ? env_image[i] : (uint8_t)quickproof_rnd();
        return;
    }
#ifdef GP_RUNS
    /* The prior scratch under the interpreter: a cheap pattern with no zero byte, not one draw per byte. */
    uint8_t seed = (uint8_t)(1u + env_r(255));
    for (size_t i = 0; i < n; ++i)
        buf[i] = (uint8_t)(seed + (uint8_t)i) | 1u;
#else
    for (size_t i = 0; i < n; ++i)
        buf[i] = (uint8_t)quickproof_rnd();
#endif
}
