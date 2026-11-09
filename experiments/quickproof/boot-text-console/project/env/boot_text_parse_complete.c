/* Value distributions of the law boot_text_parse_complete for native and interpreter runs (not part of any
 * theorem).  The law draws pitch, width, height, the number of other tags, their types and sizes and the
 * framebuffer tag's size from nondet_u32, in that order; drawing them by call index makes most runs pass the
 * law's assumptions (each run is a fresh process, so the counter starts at 0). */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

static unsigned env_calls;
static uint32_t env_pitch;

uint32_t nondet_u32(void) {
    uint64_t r = quickproof_rnd();
    switch (env_calls++) {
    case 0:                                             /* pitch: even, 2..512, often a boundary */
        env_pitch = r % 4 == 0 ? 512u : r % 4 == 1 ? 2u : (uint32_t)(2 + 2 * ((r >> 8) % 256));
        return env_pitch;
    case 1: {                                           /* width: 1..min(160, pitch/2) */
        uint32_t most = env_pitch / 2 < 160 ? env_pitch / 2 : 160;
        return r % 4 == 0 ? most : (uint32_t)(1 + (r >> 8) % most);
    }
    case 2: return r % 4 == 0 ? 64u : r % 4 == 1 ? 1u : (uint32_t)(1 + (r >> 8) % 64);   /* height */
    case 3: return (uint32_t)(r % 3);                                                   /* other tags */
    case 4: case 6: return (uint32_t)(1 + r % 22) == 8 ? 9u : (uint32_t)(1 + r % 22);  /* their types */
    case 5: case 7: return (uint32_t)(8 + r % 57);                                      /* their sizes */
    case 8: return (uint32_t)(32 + r % 33);                                             /* framebuffer tag */
    default: return (uint32_t)r;
    }
}

uint8_t nondet_u8(void) { return (uint8_t)quickproof_rnd(); }
size_t nondet_size(void) { return (size_t)(quickproof_rnd() % 4096); }
void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
}
