/* Value distributions of the law window_roots_isolated for native and interpreter runs (not part of any
 * theorem).  nondet_size serves the law's draws by call index (each run is a fresh process).  A plan made at
 * the first draw picks a window of one or two pages (often at the 16 MiB top, slot 1 or the last slots),
 * places the four roots, gives the source the table entries its placement names, zero leaves at the alias
 * slots and leaves drawn from a small frame set around the window's frames, and an inventory holding the
 * window's frames; then sometimes breaks one rule.  nondet_u32 draws the built flag: usually 0, sometimes
 * set with a first record that matches this build or not. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

#define ENV_ROOT UINT64_C(45056)
#define ENV_P UINT64_C(1)
#define ENV_W UINT64_C(2)
#define ENV_U UINT64_C(4)
#define ENV_A UINT64_C(0x20)
#define ENV_NX (UINT64_C(1) << 63)

static unsigned long env_calls;
static int env_planned, env_built;
static uint64_t env_phys[4], env_leaf[4096], env_frame[16], env_base, env_limit, env_slot;
static size_t env_n;

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

static int env_member(uint64_t f) {
    for (size_t i = 0; i < env_n && i < 16; ++i)
        if (env_frame[i] == f) return 1;
    return 0;
}

static void env_plan(void) {
    uint64_t pages = env_r(2) ? 1 : 2;
    uint64_t top = UINT64_C(0x1000000) / 4096u - pages;   /* highest first frame below 16 MiB */
    uint64_t first = env_r(4) == 0 ? top : 16u + env_r(64);
    env_base = first << 12;
    env_limit = env_base + pages * 4096u;
    uint64_t r = env_r(4);
    env_slot = r == 0 ? 1 : r == 1 ? 4096u - pages : 256u + env_r(1024);
    switch (env_r(20)) {
    case 0: env_base += 8u; env_limit += 8u; break;                    /* misaligned window */
    case 1: env_limit = env_base + 3u * 4096u; break;
    case 2: env_slot = 0; break;
    case 3: env_slot = 4097u - pages; break;
    case 4: env_limit = env_base; break;
    case 5: env_base = UINT64_C(0x1000000); env_limit = env_base + 4096u; break;
    default: break;
    }
    uint64_t at = UINT64_C(0x100000) + 4096u * env_r(1024);
    for (unsigned i = 0; i < 4; ++i) env_phys[i] = at + i * ENV_ROOT;
    if (env_r(20) == 0) env_phys[1 + env_r(3)] = env_phys[0];
    if (env_r(20) == 0) env_phys[3] = env_phys[2] + 4096u * env_r(11);   /* fetch and send overlap */
    if (env_r(24) == 0) env_phys[env_r(4)] += 8u;
    for (unsigned p = 0; p < 4096; ++p) {
        uint64_t q = env_r(32);
        uint64_t frame = env_r(3) == 0 ? first + env_r(pages) : env_r(48);
        env_leaf[p] = q < 4 ? 0 : (frame << 12) | ENV_P | (env_r(2) ? ENV_W : 0) | (env_r(2) ? ENV_U : 0) |
            (env_r(2) ? ENV_NX : 0) | (env_r(4) == 0 ? ENV_A : 0);
    }
    for (uint64_t i = 0; i < pages && env_slot + i < 4096u; ++i)
        if (env_r(24) != 0) env_leaf[env_slot + i] = 0;
    env_n = env_r(12) == 0 ? (env_r(2) ? 0 : 17) : (size_t)(pages + env_r(16 - pages + 1));
    if (env_n > 16) env_n = env_r(2) ? 16 : env_n;
    for (unsigned i = 0; i < 16; ++i) {
        uint64_t f;
        int again;
        do {
            f = i < pages ? first + i : env_r(64);
            again = 0;
            for (unsigned j = 0; j < i; ++j) again |= env_frame[j] == f;
        } while (again);
        env_frame[i] = f;
    }
    if (env_r(4) == 0) {                                   /* the window's frames elsewhere in the list */
        uint64_t t = env_frame[0]; size_t j = env_n > 1 && env_n <= 16 ? env_n - 1 : 0;
        env_frame[0] = env_frame[j]; env_frame[j] = t;
    }
    if (env_r(20) == 0) env_frame[env_r(pages)] = 64u + env_r(64);   /* a window frame left out */
    env_built = env_r(4) == 0;
    env_planned = 1;
}

static uint64_t env_upper(unsigned long k) {
    unsigned long i = k / 3, which = k % 3;
    uint64_t phys = env_phys[0], accessed = env_r(4) == 0 ? ENV_A : 0, v;
    if (which == 0) v = i == 0 ? ((phys + 4096u) | 7u | accessed) : 0;
    else if (which == 1) v = i == 0 ? ((phys + 8192u) | 7u | accessed) : 0;
    else v = (i < 8 ? ((phys + 4096u * (3 + i)) | 7u) : 0) | accessed;
    if (env_r(4096) == 0) v ^= UINT64_C(1) << env_r(64);
    return v;
}

static uint64_t env_first(unsigned long k) {             /* the prior first record */
    if (!env_built || env_r(8) == 0) return quickproof_rnd();
    uint64_t removed = 0, retained = 0;
    for (unsigned p = 0; p < 4096; ++p) {
        uint64_t s = env_leaf[p];
        if ((s & ENV_P) && env_member((s & UINT64_C(0x000ffffffffff000)) >> 12)) ++removed;
        else if (s & ENV_P) ++retained;
    }
    return k == 0 ? env_n : k == 1 ? removed : k == 2 ? retained : quickproof_rnd();
}

size_t nondet_size(void) {
    unsigned long k = env_calls++;
    if (!env_planned) env_plan();
    if (k < 4) return env_phys[k];
    k -= 4;
    if (k < 1536) return env_upper(k);
    k -= 1536;
    if (k < 4096) return env_leaf[k];
    k -= 4096;
    if (k == 0) return env_n;
    k -= 1;
    if (k < 16) return env_frame[k];
    k -= 16;
    if (k == 0) return env_base;
    if (k == 1) return env_limit;
    if (k == 2) return env_slot;
    return env_first(k - 3);
}

uint32_t nondet_u32(void) {
    if (!env_planned) env_plan();
    return env_built ? (env_r(4) == 0 ? 7u : 1u) : 0u;
}

uint8_t nondet_u8(void) { return (uint8_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
