/* Value distributions of the law window_scan_exact for native and interpreter runs (not part of any theorem).
 * nondet_size serves the law's draws by call index (each run is a fresh process).  A plan made at the first
 * draw builds a closed root at its physical address with leaves outside the inventory, and a root that is the
 * closed root plus the exact aliases of a window, so that most runs pass the scan; then it sometimes breaks
 * one thing: a table entry, a leaf, an alias's permission, a protected frame left in the closed root (in
 * both roots), or the window's geometry (including slots near 2^64, whose sum wraps).  nondet_u8 draws the
 * writable flag the plan chose, or the other one. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

#define ENV_P UINT64_C(1)
#define ENV_W UINT64_C(2)
#define ENV_U UINT64_C(4)
#define ENV_A UINT64_C(0x20)
#define ENV_NX (UINT64_C(1) << 63)

static unsigned long env_calls;
static int env_planned, env_writable;
static uint64_t env_phys[2], env_upper[2][1536], env_leaf[2][4096], env_frame[16];
static uint64_t env_base, env_limit, env_slot;
static size_t env_n;

static uint64_t env_r(uint64_t bound) { return quickproof_rnd() % bound; }

static void env_tables(unsigned r) {
    uint64_t phys = env_phys[r];
    for (unsigned k = 0; k < 1536; ++k) {
        unsigned i = k / 3, which = k % 3;
        uint64_t accessed = env_r(4) == 0 ? ENV_A : 0, v;
        if (which == 0) v = i == 0 ? ((phys + 4096u) | 7u | accessed) : 0;
        else if (which == 1) v = i == 0 ? ((phys + 8192u) | 7u | accessed) : 0;
        else v = (i < 8 ? ((phys + 4096u * (3 + i)) | 7u) : 0) | accessed;
        env_upper[r][k] = v;
    }
}

static void env_plan(void) {
    env_phys[0] = UINT64_C(0x100000) + 4096u * env_r(4096);
    env_phys[1] = UINT64_C(0x100000) + 4096u * env_r(4096);
    env_tables(0);
    env_tables(1);
    env_n = (size_t)env_r(17);
    for (unsigned i = 0; i < 16; ++i) env_frame[i] = env_r(64);
    uint64_t pages = 1 + env_r(2), first = env_r(48);
    env_base = first << 12;
    env_limit = env_base + pages * 4096u;
    env_slot = env_r(4) == 0 ? 4096u - pages : 1 + env_r(4000);
    switch (env_r(16)) {
    case 0: env_limit = env_base + 4096u * (3 + env_r(4)); break;        /* more pages */
    case 1: env_base += 8u; break;                                       /* limit - base not a page multiple */
    case 2: env_slot = UINT64_MAX - env_r(2); break;                     /* slot + pages wraps */
    case 3: env_limit = env_base - 4096u; break;                         /* limit below base */
    default: break;
    }
    uint64_t span = (env_limit - env_base) / 4096u;
    env_writable = (int)env_r(2);
    for (unsigned p = 0; p < 4096; ++p) {
        uint64_t f = env_r(128), leaf;
        if (env_r(8) == 0) leaf = 0;
        else {
            int is_inv = 0;
            for (size_t i = 0; i < env_n; ++i) is_inv |= env_frame[i] == f;
            if (is_inv) f = 64u + env_r(64);
            leaf = (f << 12) | ENV_P | (env_r(2) ? ENV_W : 0) | (env_r(2) ? ENV_U : 0) |
                (env_r(2) ? ENV_NX : 0) | (env_r(4) == 0 ? ENV_A : 0);
        }
        env_leaf[1][p] = leaf;
        env_leaf[0][p] = (uint64_t)p >= env_slot && (uint64_t)p < env_slot + span
            ? (((env_base >> 12) + ((uint64_t)p - env_slot)) << 12) | ENV_P | ENV_NX |
              (env_writable ? ENV_W : 0)
            : leaf;
    }
    switch (env_r(12)) {
    case 0: env_upper[env_r(2)][env_r(1536)] ^= UINT64_C(1) << env_r(64); break;
    case 1: env_leaf[0][env_r(4096)] ^= UINT64_C(1) << env_r(64); break;
    case 2: if (env_n > 0) {                                             /* a protected frame, in both */
                unsigned p = (unsigned)env_r(4096);
                env_leaf[1][p] = (env_frame[env_r(env_n)] << 12) | ENV_P;
                if (!((uint64_t)p >= env_slot && (uint64_t)p < env_slot + span)) env_leaf[0][p] = env_leaf[1][p];
            }
            break;
    case 3: env_writable = !env_writable; break;     /* the scan is asked about the other permission */
    default: break;
    }
    env_planned = 1;
}

size_t nondet_size(void) {
    unsigned long k = env_calls++;
    if (!env_planned) env_plan();
    if (k < 2) return env_phys[k];
    k -= 2;
    for (unsigned r = 0; r < 2; ++r) {
        if (k < 1536) return env_upper[r][k];
        k -= 1536;
        if (k < 4096) return env_leaf[r][k];
        k -= 4096;
    }
    if (k == 0) return env_n;
    k -= 1;
    if (k < 16) return env_frame[k];
    k -= 16;
    if (k == 0) return env_base;
    if (k == 1) return env_limit;
    if (k == 2) return env_slot;
    return quickproof_rnd();
}

uint8_t nondet_u8(void) {
    if (!env_planned) env_plan();
    return (uint8_t)(env_writable | (env_r(128) << 1));
}

uint32_t nondet_u32(void) { return (uint32_t)quickproof_rnd(); }

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
