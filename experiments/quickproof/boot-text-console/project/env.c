/* Value distributions for the native and interpreter runs of leanos_console (not part of any theorem).
 * Uniform bytes almost never form a Multiboot2 tag chain, so nondet_bytes mostly writes a well-formed chain
 * (fixed header, then tags of random types and sizes, a framebuffer tag with a boundary geometry, an end tag)
 * and then sometimes corrupts one field.  nondet_u8 drives the harness's print loop: it ends a run with
 * probability about 1/1500 and otherwise yields printable bytes, CR, LF and control bytes. */
#include <stddef.h>
#include <stdint.h>
#include "quickproof.h"

extern uint64_t quickproof_rnd(void);

static void env_put32(uint8_t *p, uint32_t v) {
    for (unsigned i = 0; i < 4; ++i) p[i] = (uint8_t)(v >> (8 * i));
}

static uint32_t env_pick_of(const uint32_t *values, unsigned count) {
    return values[quickproof_rnd() % count];
}

size_t nondet_size(void) {
    switch (quickproof_rnd() % 4) {
    case 0: return (size_t)(quickproof_rnd() % 64);
    case 1: return (size_t)(quickproof_rnd() % 512);
    case 2: return (size_t)((quickproof_rnd() % 64) * 8);
    default: return (size_t)(quickproof_rnd() % 4096);
    }
}

uint32_t nondet_u32(void) { return (uint32_t)quickproof_rnd(); }

uint8_t nondet_u8(void) {
    uint64_t r = quickproof_rnd() % 1500;
    if (r == 0) return 0;
    if (r < 75) return '\n';
    if (r < 105) return '\r';
    if (r < 130) return (uint8_t)(quickproof_rnd() % 32);
    if (r < 150) return (uint8_t)(127 + quickproof_rnd() % 129);
    return (uint8_t)(32 + quickproof_rnd() % 95);
}

static void env_geometry(uint8_t *tag) {
    static const uint32_t widths[] = {0, 1, 2, 79, 80, 159, 160, 161, 0xffffffffu};
    static const uint32_t heights[] = {0, 1, 2, 24, 25, 63, 64, 65, 0xffffffffu};
    uint32_t w = quickproof_rnd() % 3 ? (uint32_t)(1 + quickproof_rnd() % 160) : env_pick_of(widths, 9);
    uint32_t h = quickproof_rnd() % 3 ? (uint32_t)(1 + quickproof_rnd() % 64) : env_pick_of(heights, 9);
    uint32_t pitch;
    switch (quickproof_rnd() % 5) {
    case 0: pitch = 2 * w; break;
    case 1: pitch = 512; break;
    case 2: pitch = 2 * w + 2 * (uint32_t)(quickproof_rnd() % 64); break;
    case 3: pitch = 2 * w - 1; break;
    default: pitch = (uint32_t)(quickproof_rnd() % 600); break;
    }
    uint64_t address = quickproof_rnd() % 8 ? 0xb8000u : (quickproof_rnd() % 2 ? 0xb8002u : quickproof_rnd());
    env_put32(tag + 8, (uint32_t)address);
    env_put32(tag + 12, (uint32_t)(address >> 32));
    env_put32(tag + 16, pitch);
    env_put32(tag + 20, w);
    env_put32(tag + 24, h);
    tag[28] = quickproof_rnd() % 8 ? 16 : (uint8_t)quickproof_rnd();
    tag[29] = quickproof_rnd() % 8 ? 2 : (uint8_t)(quickproof_rnd() % 4);
}

void nondet_bytes(uint8_t *buf, size_t n) {
    for (size_t i = 0; i < n; ++i) buf[i] = (uint8_t)quickproof_rnd();
    if (n < 16 || quickproof_rnd() % 5 == 0) return;
    /* The chain is built in a virtual buffer of `total` bytes, of which the first n are stored: a total
     * larger than n is a bootloader that claims more than is available. */
    size_t total = n & ~(size_t)7;
    if (total > 65536) total = 65536;
    if (quickproof_rnd() % 8 == 0) total += 8 * (1 + quickproof_rnd() % 8);
    uint8_t v[65536 + 128];
    for (size_t i = 0; i < total && i < sizeof v; ++i) v[i] = i < n ? buf[i] : (uint8_t)quickproof_rnd();
    env_put32(v, (uint32_t)total);
    env_put32(v + 4, quickproof_rnd() % 16 ? 0 : 1);
    size_t offset = 8;
    int framebuffers = 0;
    while (offset + 16 <= total) {
        size_t room = total - 8 - offset;
        uint32_t type = (uint32_t)(quickproof_rnd() % 4 == 0 ? quickproof_rnd() % 22 : 8);
        if (type == 8 && framebuffers && quickproof_rnd() % 4) type = 1;
        if (type == 0) type = 1;
        size_t size = type == 8 ? 32 + quickproof_rnd() % 9 : 8 + quickproof_rnd() % 40;
        if (quickproof_rnd() % 64 == 0) size = 0xfffffff8u + quickproof_rnd() % 8;   /* wraps when rounded */
        else if (quickproof_rnd() % 32 == 0) size = room + 8 + quickproof_rnd() % 64; /* runs past the end */
        else if (size > room) break;
        env_put32(v + offset, type);
        env_put32(v + offset + 4, (uint32_t)size);
        if (type == 8 && offset + 30 <= total) { env_geometry(v + offset); ++framebuffers; }
        if (size > room) break;
        offset += (size + 7) & ~(size_t)7;
        if (quickproof_rnd() % 3 == 0) break;
    }
    if (offset + 8 <= total) {
        env_put32(v + offset, 0);
        env_put32(v + offset + 4, 8);
        if (quickproof_rnd() % 4) {                          /* make the end tag the last one */
            total = offset + 8;
            env_put32(v, (uint32_t)total);
        }
    }
    for (size_t i = 0; i < n && i < total; ++i) buf[i] = v[i];
    if (quickproof_rnd() % 6 == 0) buf[quickproof_rnd() % n] ^= (uint8_t)(1u << (quickproof_rnd() % 8));
}
