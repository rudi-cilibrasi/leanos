/* Value distributions of the law enumeration_exact for native and interpreter runs (not part of any theorem).
 * The law draws the prior snapshot count (u32), the prior result location (4 u8), the three NULL choices (3 u8),
 * then, per read, whether it fails (u8) and, when it succeeds, its value (u32).  A uniform device would almost never
 * answer a vendor of 0xffff, so it would find a 17th function within 17 reads.  This plan makes most identity reads
 * absent and picks, per run, how many functions are present (none, a few, about the capacity, many) and whether and
 * where a read fails, so that runs reach OK, CAPACITY_EXCEEDED and READ_FAILED at every depth of the segment.  It
 * follows the scan's order to know which value is an identity. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

static int env_planned;
static unsigned long env_u8_calls, env_u32_calls, env_reads;
static uint64_t env_present_inverse;   /* an identity read is present with probability 1 / this; 0: never */
static unsigned long env_fail_at;      /* the read that fails; ULONG_MAX: none */
static unsigned env_pending, env_found;

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

static void env_plan(void) {
    static const uint64_t inverse[4] = {0, 8192, 3855, 64};   /* expected 0, 8, 17 and 1024 present functions */
    env_present_inverse = inverse[env_r(4)];
    env_fail_at = env_r(2) == 0 ? (unsigned long)-1 : (unsigned long)env_r(65536 + 16 * 15);
    env_planned = 1;
}

uint8_t nondet_u8(void) {
    if (!env_planned) env_plan();
    unsigned long k = env_u8_calls++;
    if (k < 4) return (uint8_t)quickproof_rnd();                 /* the prior result location */
    if (k < 7) return (uint8_t)(env_r(8) == 0 ? 0 : 1);           /* NULL with probability 1/8 each */
    unsigned long read = env_reads++;
    return (uint8_t)(read == env_fail_at ? 0 : 1 + env_r(255));   /* 0: this read fails */
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    unsigned long k = env_u32_calls++;
    if (k == 0) return (uint32_t)quickproof_rnd();                /* the prior snapshot count */
    if (env_pending > 0) {                                        /* a dword of the function just found */
        --env_pending;
        return (uint32_t)quickproof_rnd();
    }
    if (env_present_inverse != 0 && env_r(env_present_inverse) == 0) {
        if (env_found < 16) env_pending = 15;
        ++env_found;
        return ((uint32_t)quickproof_rnd() & 0xffff0000u) | (uint32_t)env_r(0xffff);
    }
    return (uint32_t)quickproof_rnd() | 0xffffu;                  /* absent: vendor 0xffff */
}

size_t nondet_size(void) { return (size_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
