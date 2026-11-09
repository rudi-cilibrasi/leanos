/* Value distributions of the law capabilities_complete for native and interpreter runs (not part of any theorem).
 * The law draws 64 space words, the count, the offsets, the ids, then (for an empty list) the head form, then bus,
 * device and function, and assumes a well-formed list; nondet_u32 serves those draws by call index from a plan
 * made at the first draw so that most runs pass the assumptions: distinct aligned offsets from a shuffle of the
 * 48 slots, ids below 0xff, a header with a valid vendor and header type, an in-range device and function. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

static int env_planned;
static unsigned long env_u8_calls, env_u32_calls;
static uint32_t env_n, env_at[48];

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

static void env_plan(void) {
    unsigned slots[48];
    for (unsigned i = 0; i < 48; ++i) slots[i] = i;
    for (unsigned i = 47; i > 0; --i) { unsigned j = (unsigned)env_r(i + 1), t = slots[i]; slots[i] = slots[j]; slots[j] = t; }
    env_n = env_r(4) == 0 ? 48 : (uint32_t)env_r(9);
    for (unsigned i = 0; i < 48; ++i) env_at[i] = 64 + 4 * slots[i];
    env_planned = 1;
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    unsigned long k = env_u32_calls++;
    if (k < 64) {
        uint32_t w = (uint32_t)quickproof_rnd();
        if (k == 0) w = (w & 0xffff0000u) | (uint32_t)env_r(0xffff);
        if (k == 3) w = (w & ~0x007f0000u) | ((uint32_t)env_r(2) << 16);
        return w;
    }
    k -= 64;
    if (k == 0) return env_n;
    k -= 1;
    if (k < env_n) return env_at[k];
    k -= env_n;
    if (k < env_n) return (uint32_t)env_r(255);
    return (uint32_t)quickproof_rnd();
}

uint8_t nondet_u8(void) {
    unsigned long k = env_u8_calls++;
    if (env_n > 0) k += 1;                            /* no head-form draw for a nonempty list */
    if (k == 0) return (uint8_t)env_r(2);             /* the empty list's head form */
    if (k == 1) return (uint8_t)quickproof_rnd();     /* bus */
    if (k == 2) return (uint8_t)env_r(32);            /* device */
    return (uint8_t)env_r(8);                         /* function */
}

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
