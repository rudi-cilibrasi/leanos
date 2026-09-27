/* Runtime-free executor for Lean-authored WiFi device programs.

   The instruction set and its encoding are defined by
   LeanOS/Wifi/Bytecode.lean; this file only performs the effect that each
   instruction names. It is shared by the FreeBSD userland development runner
   and the LeanOS lab kernel, which supply the effect hooks below. */
#ifndef LEANOS_WIFI_EXEC_H
#define LEANOS_WIFI_EXEC_H

#include <stdint.h>

#define WIFI_MAGIC 0x4649574cu
#define WIFI_WINDOW_BYTES 0x4000u
#define WIFI_STACK_DEPTH 16
#define WIFI_SCRATCH_BYTES 65536u

struct wifi_hooks {
    uint32_t (*mmio_read32)(void *ctx, uint32_t off);
    uint16_t (*mmio_read16)(void *ctx, uint32_t off);
    void (*mmio_write32)(void *ctx, uint32_t off, uint32_t value);
    void (*mmio_write16)(void *ctx, uint32_t off, uint16_t value);
    uint32_t (*cfg_read32)(void *ctx, uint32_t off);
    void (*cfg_write32)(void *ctx, uint32_t off, uint32_t value);
    void (*delay_us)(void *ctx, uint32_t us);
    void (*print)(void *ctx, uint32_t tag, uint32_t value);
    void *ctx;
};

enum wifi_status {
    WIFI_HALT = 0,
    WIFI_FAIL = 1,          /* program-issued typed rejection; code in *code */
    WIFI_BAD_IMAGE = 2,
    WIFI_BAD_PC = 3,
    WIFI_BAD_OFFSET = 4,
    WIFI_BAD_OPCODE = 5,
    WIFI_STACK = 6,
    WIFI_STEP_LIMIT = 7,
    WIFI_BAD_BLOB = 8,
    WIFI_BAD_MEM = 9,
};

/* Scratch RAM for frames and protocol state; zeroed at program start. */
static uint8_t wifi_scratch[WIFI_SCRATCH_BYTES];

/* With WIFI_HOOKS_DIRECT the executor calls fixed hook functions by name
   (the LeanOS lab kernel forbids indirect control flow); otherwise it calls
   through `struct wifi_hooks`. */
#ifdef WIFI_HOOKS_DIRECT
uint32_t wifi_hook_mmio_read32(uint32_t off);
uint16_t wifi_hook_mmio_read16(uint32_t off);
void wifi_hook_mmio_write32(uint32_t off, uint32_t value);
void wifi_hook_mmio_write16(uint32_t off, uint16_t value);
uint32_t wifi_hook_cfg_read32(uint32_t off);
void wifi_hook_cfg_write32(uint32_t off, uint32_t value);
void wifi_hook_delay_us(uint32_t us);
void wifi_hook_print(uint32_t tag, uint32_t value);
#define WH_R32(o) wifi_hook_mmio_read32(o)
#define WH_R16(o) wifi_hook_mmio_read16(o)
#define WH_W32(o, v) wifi_hook_mmio_write32((o), (v))
#define WH_W16(o, v) wifi_hook_mmio_write16((o), (v))
#define WH_CR32(o) wifi_hook_cfg_read32(o)
#define WH_CW32(o, v) wifi_hook_cfg_write32((o), (v))
#define WH_DELAY(u) wifi_hook_delay_us(u)
#define WH_PRINT(t, v) wifi_hook_print((t), (v))
#else
#define WH_R32(o) h->mmio_read32(h->ctx, (o))
#define WH_R16(o) h->mmio_read16(h->ctx, (o))
#define WH_W32(o, v) h->mmio_write32(h->ctx, (o), (v))
#define WH_W16(o, v) h->mmio_write16(h->ctx, (o), (v))
#define WH_CR32(o) h->cfg_read32(h->ctx, (o))
#define WH_CW32(o, v) h->cfg_write32(h->ctx, (o), (v))
#define WH_DELAY(u) h->delay_us(h->ctx, (u))
#define WH_PRINT(t, v) h->print(h->ctx, (t), (v))
#endif

static inline uint32_t wifi_le32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

/* Execute `image` (the Lean-encoded program). `code` receives the fail code
   or the offending pc; `steps` bounds execution. */
static int wifi_exec(const uint8_t *image, uint32_t image_len,
                     const struct wifi_hooks *h, uint64_t max_steps,
                     uint32_t *code) {
    if (image_len < 16 || wifi_le32(image) != WIFI_MAGIC ||
        wifi_le32(image + 4) != 1)
        return WIFI_BAD_IMAGE;
    uint32_t n = wifi_le32(image + 8), blob_len = wifi_le32(image + 12);
    if (n > (image_len - 16) / 16 || blob_len != image_len - 16 - n * 16)
        return WIFI_BAD_IMAGE;
    const uint8_t *code_base = image + 16;
    const uint8_t *blob = code_base + (uint64_t)n * 16;
    uint32_t r[16] = {0};
    uint32_t stack[WIFI_STACK_DEPTH];
    uint32_t sp = 0, pc = 0;
    for (uint32_t i = 0; i < WIFI_SCRATCH_BYTES; ++i) wifi_scratch[i] = 0;
#ifdef WIFI_HOOKS_DIRECT
    (void)h;
#endif
    for (uint64_t step = 0; step < max_steps; ++step) {
        if (pc >= n) { *code = pc; return WIFI_BAD_PC; }
        const uint8_t *in = code_base + (uint64_t)pc * 16;
        uint32_t op = wifi_le32(in), a = wifi_le32(in + 4);
        uint32_t b = wifi_le32(in + 8), c = wifi_le32(in + 12);
        uint32_t base = op & 0xffu, imm = op & 0x100u, sub = op >> 16;
        pc++;
#define REG(x) do { if ((x) > 15) { *code = pc - 1; return WIFI_BAD_OPCODE; } } while (0)
#define OFF(x, w) do { if ((x) > WIFI_WINDOW_BYTES - (w) || ((x) & ((w) - 1))) { *code = pc - 1; return WIFI_BAD_OFFSET; } } while (0)
        switch (base) {
        case 0: *code = 0; return WIFI_HALT;
        case 1: *code = a; return WIFI_FAIL;
        case 2: REG(a); if (b > 0xffc || (b & 3)) { *code = pc - 1; return WIFI_BAD_OFFSET; }
            r[a] = WH_CR32(b); break;
        case 3: { uint32_t v = imm ? b : (b < 16 ? r[b] : 0);
            if (!imm) REG(b);
            if (a > 0xffc || (a & 3)) { *code = pc - 1; return WIFI_BAD_OFFSET; }
            WH_CW32(a, v); break; }
        case 4: REG(a); OFF(b, 4); r[a] = WH_R32(b); break;
        case 5: REG(a); OFF(b, 2); r[a] = WH_R16(b); break;
        case 6: case 7: { if (!imm) REG(b);
            uint32_t v = imm ? b : r[b];
            if (base == 6) { OFF(a, 4); WH_W32(a, v); }
            else { OFF(a, 2); WH_W16(a, (uint16_t)v); }
            break; }
        case 8: case 10: { REG(a); REG(b); uint32_t off = r[b] + c;
            if (base == 8) { OFF(off, 4); r[a] = WH_R32(off); }
            else { OFF(off, 2); r[a] = WH_R16(off); }
            break; }
        case 9: case 11: { REG(a); if (!imm) REG(c);
            uint32_t off = r[a] + b, v = imm ? c : r[c];
            if (base == 9) { OFF(off, 4); WH_W32(off, v); }
            else { OFF(off, 2); WH_W16(off, (uint16_t)v); }
            break; }
        case 12: { REG(a); if (!imm) REG(b);
            uint32_t v = imm ? b : r[b];
            switch (sub) {
            case 0: r[a] = v; break;
            case 1: r[a] += v; break;
            case 2: r[a] -= v; break;
            case 3: r[a] &= v; break;
            case 4: r[a] |= v; break;
            case 5: r[a] ^= v; break;
            case 6: r[a] = v >= 32 ? 0 : r[a] << v; break;
            case 7: r[a] = v >= 32 ? 0 : r[a] >> v; break;
            case 8: r[a] *= v; break;
            case 9: v &= 31; r[a] = v ? (r[a] << v) | (r[a] >> (32 - v)) : r[a]; break;
            default: *code = pc - 1; return WIFI_BAD_OPCODE;
            }
            break; }
        case 13: { REG(a); if (!imm) REG(b);
            uint32_t v = imm ? b : r[b], x = r[a];
            int t;
            switch (sub) {
            case 0: t = x == v; break;
            case 1: t = x != v; break;
            case 2: t = x < v; break;
            case 3: t = x >= v; break;
            default: *code = pc - 1; return WIFI_BAD_OPCODE;
            }
            if (t) pc = c;
            break; }
        case 14: pc = a; break;
        case 15: WH_DELAY(a); break;
        case 16: { if (!imm) REG(b); WH_PRINT(a, imm ? b : r[b]); break; }
        case 17: { if (b > blob_len || c > (blob_len - b) / 4 || (b & 3)) {
                *code = pc - 1; return WIFI_BAD_BLOB; }
            OFF(a, 4);
            for (uint32_t i = 0; i < c; ++i)
                WH_W32(a, wifi_le32(blob + b + 4 * i));
            break; }
        case 18: { REG(a); REG(b);
            uint64_t off = (uint64_t)c + (uint64_t)r[b] * 4;
            if ((c & 3) || off + 4 > blob_len) { *code = pc - 1; return WIFI_BAD_BLOB; }
            r[a] = wifi_le32(blob + off); break; }
        case 19: if (sp == WIFI_STACK_DEPTH) { *code = pc - 1; return WIFI_STACK; }
            stack[sp++] = pc; pc = a; break;
        case 20: if (sp == 0) { *code = pc - 1; return WIFI_STACK; }
            pc = stack[--sp]; break;
        case 21: { REG(a); REG(b);
            uint64_t at = (uint64_t)r[b] + c;
            if (at + sub > WIFI_SCRATCH_BYTES || (sub != 1 && sub != 2 && sub != 4)) {
                *code = pc - 1; return WIFI_BAD_MEM; }
            uint32_t v = 0;
            for (uint32_t i = 0; i < sub; ++i) v |= (uint32_t)wifi_scratch[at + i] << (8 * i);
            r[a] = v; break; }
        case 22: { REG(a); if (!imm) REG(c);
            uint64_t at = (uint64_t)r[a] + b;
            uint32_t v = imm ? c : r[c];
            if (at + sub > WIFI_SCRATCH_BYTES || (sub != 1 && sub != 2 && sub != 4)) {
                *code = pc - 1; return WIFI_BAD_MEM; }
            for (uint32_t i = 0; i < sub; ++i) wifi_scratch[at + i] = (uint8_t)(v >> (8 * i));
            break; }
        case 23: case 24: { REG(b); REG(c); OFF(a, 4);
            uint64_t at = r[b], n = r[c];
            if (at + 4 * n > WIFI_SCRATCH_BYTES) { *code = pc - 1; return WIFI_BAD_MEM; }
            for (uint64_t i = 0; i < n; ++i) {
                uint8_t *p = wifi_scratch + at + 4 * i;
                if (base == 23) {
                    uint32_t v = WH_R32(a);
                    p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8);
                    p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);
                } else {
                    WH_W32(a, wifi_le32(p));
                }
            }
            break; }
        default: *code = pc - 1; return WIFI_BAD_OPCODE;
        }
#undef REG
#undef OFF
    }
    *code = pc;
    return WIFI_STEP_LIMIT;
}

#endif
