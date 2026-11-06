/* Value distributions of the law capabilities_adversarial for native and interpreter runs (not part of any theorem).
 * Uniformly random reads almost never pass the walker's header checks, so a plan made at the first draw builds a
 * well-formed configuration space (a valid header and an acyclic capability list of 0..48 entries) and serves the
 * initial header from it.  The walker's read order is fixed by the values it gets: the four header words, then
 * the list head and each returned next pointer, so the env replays it and answers each read from the space.  It
 * then sometimes misbehaves: a read fails, a value is flipped, the list has a cycle, a bad or short pointer, an id
 * of 0xff, or more than 48 entries' worth of links, or the header names an out-of-range device or function.  A
 * header read changes a bit inside its word's mask about once in 4 reads, and each of the four pointer arguments
 * is NULL about once in 32 runs. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

static int env_planned;
static unsigned long env_u8_calls, env_u32_calls, env_reads;
static uint32_t env_space[64];
static uint8_t env_bus, env_device, env_function, env_pointer;

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

static void env_plan(void) {
    for (unsigned i = 0; i < 64; ++i) env_space[i] = (uint32_t)quickproof_rnd();
    env_space[0] = (env_space[0] & 0xffff0000u) |                              /* vendor, sometimes 0xffff */
        (env_r(16) == 0 ? 0xffffu : (uint32_t)env_r(0xffff));
    env_space[3] = (env_space[3] & ~0x007f0000u) |                             /* header type, sometimes > 1 */
        ((env_r(16) == 0 ? (env_r(2) ? 2u : 3u + (uint32_t)env_r(125)) : (uint32_t)env_r(2)) << 16);
    unsigned slots[48], n = env_r(4) == 0 ? 48 : (unsigned)env_r(8);
    for (unsigned i = 0; i < 48; ++i) slots[i] = i;
    for (unsigned i = 47; i > 0; --i) { unsigned j = (unsigned)env_r(i + 1), t = slots[i]; slots[i] = slots[j]; slots[j] = t; }
    for (unsigned i = 0; i < n; ++i) {
        uint32_t at = 64 + 4 * slots[i], next = i + 1 < n ? 64 + 4 * slots[i + 1] : 0;
        uint32_t id = (uint32_t)env_r(255);
        env_space[at / 4] = (env_space[at / 4] & 0xffff0000u) | (next << 8) | id;
    }
    if (n > 0) {
        env_space[1] |= 0x00100000u;
        env_space[13] = (env_space[13] & ~255u) | (64 + 4 * slots[0]);
        switch (env_r(16)) {                       /* a broken list, sometimes */
        case 0: { uint32_t last = 64 + 4 * slots[n - 1];                  /* a cycle */
                  env_space[last / 4] = (env_space[last / 4] & ~0xff00u) | ((64 + 4 * slots[env_r(n)]) << 8); break; }
        case 1: { uint32_t at = 64 + 4 * slots[env_r(n)];                 /* a misaligned or low pointer */
                  env_space[at / 4] = (env_space[at / 4] & ~0xff00u) | ((uint32_t)(env_r(2) ? 1 + 4 * env_r(60) : 4 * env_r(16)) << 8); break; }
        case 2: { uint32_t at = 64 + 4 * slots[env_r(n)]; env_space[at / 4] |= 255u; break; }    /* id 0xff */
        default: break;
        }
    } else if (env_r(2)) {
        env_space[1] &= ~0x00100000u;
    } else {
        env_space[1] |= 0x00100000u; env_space[13] &= ~255u;
    }
    env_bus = (uint8_t)quickproof_rnd();
    uint64_t r = env_r(16);                           /* device and function, often at the boundaries */
    env_device = (uint8_t)(r == 0 ? 32 : r == 1 ? 31 : r == 2 ? 33 + env_r(223) : env_r(32));
    r = env_r(16);
    env_function = (uint8_t)(r == 0 ? 8 : r == 1 ? 7 : r == 2 ? 9 + env_r(247) : env_r(8));
    env_planned = 1;
}

static uint8_t env_next_offset(void) {               /* the offset of the walker's next read */
    static const uint8_t header[4] = {0, 4, 12, 52};
    if (env_reads < 4) return header[env_reads];
    return env_pointer;
}

uint8_t nondet_u8(void) {
    if (!env_planned) env_plan();
    unsigned long k = env_u8_calls++;
    if (k == 0) return env_bus;
    if (k == 1) return env_device;
    if (k == 2) return env_function;
    if (k == 3) return (uint8_t)quickproof_rnd();    /* the result record's prior offset */
    if (k < 8) return env_r(32) == 0 ? 0 : 1;        /* callback, header, snapshot, result: NULL or present */
    return env_r(256) == 0 ? 0 : 1;                  /* a read fails about once in 256 */
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    unsigned long k = env_u32_calls++;
    if (k < 16) return env_space[k];
    if (k == 16) return (uint32_t)quickproof_rnd();  /* the prior snapshot count */
    uint8_t offset = env_next_offset();
    uint32_t v = env_space[offset / 4 & 63];
    static const uint32_t masks[4] = {0xffffffffu, 0x00100000u, 0x00ff0000u, 255u};
    if (env_reads < 4 && env_r(4) == 0) {            /* a header word changed under its mask */
        uint32_t bit;
        do bit = 1u << env_r(32); while (!(bit & masks[env_reads]));
        v ^= bit;
    } else if (env_r(128) == 0) {
        v ^= 1u << env_r(32);                         /* the device changed, or lies */
    }
    if (env_reads == 3) env_pointer = (env_space[1] & 0x00100000u) ? (uint8_t)env_space[13] : 0;
    if (env_reads >= 4) env_pointer = (uint8_t)(v >> 8);
    ++env_reads;
    return v;
}

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
