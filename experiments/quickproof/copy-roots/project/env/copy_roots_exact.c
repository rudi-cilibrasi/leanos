/* Value distributions of the law copy_roots_exact for native and interpreter runs (not part of any theorem).
 * Uniform words almost never form a source root, a valid inventory or a valid alias list, so nondet_size
 * serves the law's draws by call index (each run is a fresh process): a plan made at the first draw places
 * the three roots (often adjacent, sometimes overlapping, misaligned, zero or at the 2^52 boundary), gives
 * the source the table entries its placement names (with random Accessed bits, sometimes one corrupted),
 * leaves drawn from a small frame set so that the inventory meets them, an inventory of distinct frames and
 * aliases at pages the source leaves zero, and then sometimes breaks one rule.  nondet_u8 makes a pointer
 * argument NULL about once in 64 draws. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

#define ENV_ROOT UINT64_C(45056)
#define ENV_P UINT64_C(1)
#define ENV_W UINT64_C(2)
#define ENV_U UINT64_C(4)
#define ENV_A UINT64_C(0x20)
#define ENV_D UINT64_C(0x40)
#define ENV_NX (UINT64_C(1) << 63)
#define ENV_LIMIT (UINT64_C(1) << 52)

static unsigned long env_calls;
static uint64_t env_phys[3];
static uint64_t env_leaf[4096];
static uint64_t env_frame[16];
static size_t env_n;
static int env_planned;

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

static void env_plan(void) {
    uint64_t base = UINT64_C(0x100000) + 4096u * env_r(4096);
    uint64_t gap = env_r(4) == 0 ? ENV_ROOT : ENV_ROOT + 4096u * env_r(8);
    for (unsigned i = 0; i < 3; ++i) env_phys[i] = base + i * gap;
    if (env_r(4) == 0) {                                 /* shuffle the order */
        uint64_t t = env_phys[0]; env_phys[0] = env_phys[2]; env_phys[2] = t;
    }
    if (env_r(6) == 0) env_phys[env_r(3)] = ENV_LIMIT - ENV_ROOT;   /* the highest accepted */
    switch (env_r(24)) {
    case 0: env_phys[env_r(3)] += 8u; break;                       /* misaligned */
    case 1: env_phys[env_r(3)] = 0; break;
    case 2: env_phys[env_r(3)] = ENV_LIMIT - ENV_ROOT + 4096u; break;
    case 3: env_phys[1] = env_phys[0] + 4096u * env_r(11); break;   /* overlap */
    case 4: env_phys[2] = env_phys[1] + ENV_ROOT - 4096u; break;
    case 5: env_phys[env_r(3)] = quickproof_rnd(); break;
    default: break;
    }
    for (unsigned p = 0; p < 4096; ++p) {
        uint64_t r = env_r(64);
        if (r < 8) env_leaf[p] = 0;
        else if (r == 8) env_leaf[p] = (env_r(48) << 12) | ENV_D;  /* absent, address bits set */
        else if (r == 9) env_leaf[p] = quickproof_rnd();
        else
            env_leaf[p] = (env_r(48) << 12) | ENV_P | (env_r(2) ? ENV_W : 0) |
                (env_r(2) ? ENV_U : 0) | (env_r(2) ? ENV_NX : 0) |
                (env_r(4) == 0 ? ENV_A | ENV_D : 0);
    }
    switch (env_r(16)) {
    case 0: env_n = 0; break;
    case 1: env_n = 17; break;
    case 2: env_n = 16; break;
    case 3: env_n = (size_t)quickproof_rnd(); break;
    default: env_n = (size_t)(1 + env_r(16)); break;
    }
    for (unsigned i = 0; i < 16; ++i) {                  /* distinct frames from 0..47 */
        uint64_t f;
        int again;
        do {
            f = env_r(48);
            again = 0;
            for (unsigned j = 0; j < i; ++j) again |= env_frame[j] == f;
        } while (again && i < 48);
        env_frame[i] = f;
    }
    if (env_r(16) == 0) env_frame[env_r(16)] = env_frame[env_r(16)];        /* maybe a duplicate */
    if (env_r(24) == 0) env_frame[env_r(16)] = (UINT64_C(1) << 40) - env_r(2);
    env_planned = 1;
}

static uint64_t env_upper(unsigned long k) {             /* source PML4[i], PDPT[i], PD[i] */
    unsigned long i = k / 3, which = k % 3;
    uint64_t phys = env_phys[0], accessed = env_r(4) == 0 ? ENV_A : 0, v;
    if (which == 0) v = i == 0 ? ((phys + 4096u) | 7u | accessed) : 0;
    else if (which == 1) v = i == 0 ? ((phys + 8192u) | 7u | accessed) : 0;
    else v = (i < 8 ? ((phys + 4096u * (3 + i)) | 7u) : 0) | accessed;
    if (env_r(4096) == 0) v ^= UINT64_C(1) << env_r(64);   /* about one corrupted entry in three roots */
    return v;
}

static uint64_t env_alias(unsigned long k) {             /* aliases[k / 3]: page, frame, writable */
    unsigned long a = k / 3, field = k % 3;
    size_t n = env_n >= 1 && env_n <= 16 ? env_n : 16;
    if (field == 0) {
        if (env_r(24) == 0) return env_r(2) ? 4096u : (uint64_t)env_r(4096);   /* outside, or any page */
        for (unsigned tries = 0; tries < 64; ++tries) {
            uint64_t p = a == 0 ? env_r(2048) : 2048u + env_r(2048);
            if (env_leaf[p] == 0) return p;
        }
        return 4095u;
    }
    if (field == 1) {
        if (env_r(24) == 0) return 48u + env_r(16);                         /* not in the inventory */
        return env_frame[a == 0 ? 0 : (n > 1 ? 1 : 0)];
    }
    return env_r(24) == 0 ? 2u + env_r(3) : env_r(2);
}

size_t nondet_size(void) {
    unsigned long k = env_calls++;
    if (!env_planned) env_plan();
    if (k < 3) return env_phys[k];
    k -= 3;
    if (k < 1536) return env_upper(k);
    k -= 1536;
    if (k < 4096) return env_leaf[k];
    k -= 4096;
    if (k < 2 * 5632) return quickproof_rnd();           /* prior contents of closed and copy */
    k -= 2 * 5632;
    if (k == 0) return env_n;
    k -= 1;
    if (k < 16) return env_frame[k];
    k -= 16;
    if (k == 0) {
        uint64_t r = env_r(16);
        return r == 0 ? 0 : r == 1 ? 3 : r < 6 ? 1 : 2;
    }
    k -= 1;
    if (k < 6) return env_alias(k);
    return quickproof_rnd();                              /* the prior result record */
}

uint8_t nondet_u8(void) { return env_r(64) == 0 ? 0 : (uint8_t)(1 + env_r(255)); }
uint32_t nondet_u32(void) { return (uint32_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
