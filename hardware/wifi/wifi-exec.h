/* Runtime-free executor for Lean-authored WiFi device programs.

   The instruction set and its encoding are defined by
   LeanOS/Wifi/Bytecode.lean; this file only performs the effect that each
   instruction names. It is shared by the FreeBSD userland development runner
   and the LeanOS lab kernel, which supply the effect hooks below. */
#ifndef LEANOS_WIFI_EXEC_H
#define LEANOS_WIFI_EXEC_H

#include <stdint.h>

#define WIFI_MAGIC 0x4649574cu
#define WIFI_WINDOW_BYTES 0x4000u        /* version-1 (Broadcom) window */
#define WIFI_WINDOW_MAX 0x10000u
#define WIFI_STACK_DEPTH 16
#define WIFI_SCRATCH_BYTES 262144u
#define WIFI_MAX_SINKS 8

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
    /* Physical address of scratch + off, or NULL when scratch is not
       DMA-capable (the program then sees 0). */
    uint32_t (*phys)(void *ctx, uint32_t off);
    uint8_t (*mmio_read8)(void *ctx, uint32_t off);
    void (*mmio_write8)(void *ctx, uint32_t off, uint8_t value);
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
    WIFI_POLICY = 10,       /* effect outside the image's declared policy */
    WIFI_YIELD = 11,        /* opcode 27: value in *code; resume continues */
};

/* Scratch RAM for frames, protocol state and (where the executor provides
   physical addresses) DMA structures; zeroed at program start. Accessed
   through volatile pointers because devices may write it by DMA. */
static uint8_t wifi_scratch[WIFI_SCRATCH_BYTES] __attribute__((aligned(65536)));

/* PCI function an image drives. Version-1 images imply the BCM43224. */
struct wifi_target {
    uint32_t bus, dev, fn, id, window, bar;  /* bar: config offset 0x10-0x24 */
};

/* Confinement policy declared by a version-3 image (Policy in
   LeanOS/Wifi/Bytecode.lean). Configuration bitmaps cover dword offsets
   below 0x100; the command register changes only through opcode 26 within
   the clear/set masks; `dma` admits physAddr. Address sinks are the low
   dwords of 64-bit MMIO address registers: only write32 of an in-scratch
   bus address (low) or zero (high) may touch them. Older images carry none. */
struct wifi_policy {
    uint32_t present, dma, window;
    uint64_t cfg_read, cfg_write;
    uint32_t cmd_clear, cmd_set;
    uint32_t sink_count, sinks[WIFI_MAX_SINKS];
};

static inline int wifi_is_sink(const struct wifi_policy *p, uint32_t off) {
    for (uint32_t i = 0; i < p->sink_count; ++i)
        if (p->sinks[i] == off) return 1;
    return 0;
}

/* Policy.sinkTouch: `off` lies in some sink's 8 bytes. */
static inline int wifi_sink_touch(const struct wifi_policy *p, uint32_t off) {
    for (uint32_t i = 0; i < p->sink_count; ++i)
        if (off - p->sinks[i] < 8u) return 1;
    return 0;
}

/* Policy.sinkOk: base is the bus address of scratch byte 0. */
static inline int wifi_sink_ok(const struct wifi_policy *p, uint32_t base,
                               uint32_t off, uint32_t v) {
    if (!wifi_sink_touch(p, off)) return 1;
    if (wifi_is_sink(p, off)) return v - base < WIFI_SCRATCH_BYTES;
    if (wifi_is_sink(p, off - 4u)) return v == 0;
    return 0;
}

static inline int wifi_cfg_allowed(uint64_t bits, uint32_t off) {
    return off < 0x100u && !(off & 3u) && ((bits >> (off / 4u)) & 1u);
}

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
uint32_t wifi_hook_phys(uint32_t off);
uint8_t wifi_hook_mmio_read8(uint32_t off);
void wifi_hook_mmio_write8(uint32_t off, uint8_t value);
#define WH_PHYS(o) wifi_hook_phys(o)
#define WH_R8(o) wifi_hook_mmio_read8(o)
#define WH_W8(o, v) wifi_hook_mmio_write8((o), (v))
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
#define WH_PHYS(o) (h->phys ? h->phys(h->ctx, (o)) : 0u)
#define WH_R8(o) h->mmio_read8(h->ctx, (o))
#define WH_W8(o, v) h->mmio_write8(h->ctx, (o), (v))
#endif

static inline uint32_t wifi_le32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

/* Parse the image header: target, policy and header length. 0 on success. */
static int wifi_image_header(const uint8_t *image, uint32_t image_len,
                             struct wifi_target *t, struct wifi_policy *pol,
                             uint32_t *header_len) {
    if (image_len < 16 || wifi_le32(image) != WIFI_MAGIC)
        return WIFI_BAD_IMAGE;
    uint32_t version = wifi_le32(image + 4);
    pol->present = 0; pol->dma = 0; pol->window = 0;
    pol->cfg_read = 0; pol->cfg_write = 0; pol->cmd_clear = 0; pol->cmd_set = 0;
    pol->sink_count = 0;
    if (version == 1) {
        t->bus = 2; t->dev = 0; t->fn = 0;
        t->id = 0x435314e4u; t->window = WIFI_WINDOW_BYTES; t->bar = 0x10;
        *header_len = 16;
        return 0;
    }
    if ((version != 2 && version != 3) || image_len < (version == 3 ? 68u : 32u))
        return WIFI_BAD_IMAGE;
    uint32_t bdf = wifi_le32(image + 16);
    t->bus = (bdf >> 16) & 0xffu; t->dev = (bdf >> 8) & 0x1fu; t->fn = bdf & 7u;
    t->id = wifi_le32(image + 20);
    t->window = wifi_le32(image + 24);
    t->bar = wifi_le32(image + 28) ? wifi_le32(image + 28) : 0x10u;
    if (t->bar < 0x10u || t->bar > 0x24u || (t->bar & 3u))
        return WIFI_BAD_IMAGE;
    if (t->window == 0 || t->window > WIFI_WINDOW_MAX || (t->window & 0x7ffu) ||
        (bdf & ~0xff1f07u))
        return WIFI_BAD_IMAGE;
    *header_len = 32;
    if (version == 3) {
        uint32_t flags = wifi_le32(image + 32);
        pol->present = 1;
        pol->dma = flags & 1u;
        pol->window = wifi_le32(image + 36);
        pol->cfg_read = wifi_le32(image + 40) | ((uint64_t)wifi_le32(image + 44) << 32);
        pol->cfg_write = wifi_le32(image + 48) | ((uint64_t)wifi_le32(image + 52) << 32);
        pol->cmd_clear = wifi_le32(image + 56);
        pol->cmd_set = wifi_le32(image + 60);
        pol->sink_count = image_len >= 68 ? wifi_le32(image + 64) : 0xffffffffu;
        if ((flags & ~1u) || t->window > pol->window || pol->sink_count > WIFI_MAX_SINKS ||
            image_len < 68u + 4u * pol->sink_count)
            return WIFI_BAD_IMAGE;
        for (uint32_t i = 0; i < pol->sink_count; ++i)
            pol->sinks[i] = wifi_le32(image + 68 + 4 * i);
        *header_len = 68 + 4 * pol->sink_count;
    }
    return 0;
}

/* Resumable executor state. `wifi_start` parses an image and zeroes the
   registers and scratch; `wifi_resume` runs until the program halts, fails,
   faults, yields (opcode 27) or the step count reaches `step_limit`. After a
   yield, the next resume continues with the following instruction. */
struct wifi_vm {
    const uint8_t *code_base, *blob;
    uint32_t n, blob_len, window;
    struct wifi_policy pol;
    struct wifi_target target;
    uint32_t r[16], stack[WIFI_STACK_DEPTH], sp, pc;
    uint64_t steps;
};

static int wifi_start(struct wifi_vm *vm, const uint8_t *image, uint32_t image_len) {
    uint32_t hdr = 0;
    if (wifi_image_header(image, image_len, &vm->target, &vm->pol, &hdr))
        return WIFI_BAD_IMAGE;
    uint32_t n = wifi_le32(image + 8), blob_len = wifi_le32(image + 12);
    if (n > (image_len - hdr) / 16 || blob_len != image_len - hdr - n * 16)
        return WIFI_BAD_IMAGE;
    vm->window = vm->target.window;
    vm->n = n;
    vm->blob_len = blob_len;
    vm->code_base = image + hdr;
    vm->blob = vm->code_base + (uint64_t)n * 16;
    for (unsigned i = 0; i < 16; ++i) vm->r[i] = 0;
    vm->sp = 0; vm->pc = 0; vm->steps = 0;
    volatile uint8_t *const S = wifi_scratch;
    for (uint32_t i = 0; i < WIFI_SCRATCH_BYTES; ++i) S[i] = 0;
    return 0;
}

/* Run a started program. `code` receives the fail code, the yielded value or
   the offending pc; `step_limit` bounds the total steps since `wifi_start`.
   Every check mirrors `exec` in LeanOS/Wifi/Sim.lean, in the same order. */
static int wifi_resume(struct wifi_vm *vm, const struct wifi_hooks *h,
                       uint64_t step_limit, uint32_t *code) {
    const uint32_t window = vm->window, n = vm->n, blob_len = vm->blob_len;
    const uint8_t *const code_base = vm->code_base, *const blob = vm->blob;
    const struct wifi_policy pol = vm->pol;
    volatile uint8_t *const S = wifi_scratch;
    uint32_t *const r = vm->r, *const stack = vm->stack;
    uint32_t sp = vm->sp, pc = vm->pc;
    int st;
#ifdef WIFI_HOOKS_DIRECT
    (void)h;
#endif
    while (vm->steps < step_limit) {
        vm->steps++;
        if (pc >= n) { *code = pc; st = WIFI_BAD_PC; goto out; }
        const uint8_t *in = code_base + (uint64_t)pc * 16;
        uint32_t op = wifi_le32(in), a = wifi_le32(in + 4);
        uint32_t b = wifi_le32(in + 8), c = wifi_le32(in + 12);
        uint32_t base = op & 0xffu, imm = op & 0x100u, sub = op >> 16;
        pc++;
#define REG(x) do { if ((x) > 15) { *code = pc - 1; st = WIFI_BAD_OPCODE; goto out; } } while (0)
#define OFF(x, w) do { if ((x) > window - (w) || ((x) & ((w) - 1))) { *code = pc - 1; st = WIFI_BAD_OFFSET; goto out; } } while (0)
#define POLICY(ok) do { if (pol.present && !(ok)) { *code = pc - 1; st = WIFI_POLICY; goto out; } } while (0)
#define SINK_OK(o, v) wifi_sink_ok(&pol, WH_PHYS(0), (o), (v))
#define NO_SINK(o) (!wifi_sink_touch(&pol, (o)))
        switch (base) {
        case 0: *code = 0; { st = WIFI_HALT; goto out; }
        case 1: *code = a; { st = WIFI_FAIL; goto out; }
        case 2: REG(a); if (b > 0xffc || (b & 3)) { *code = pc - 1; { st = WIFI_BAD_OFFSET; goto out; } }
            POLICY(wifi_cfg_allowed(pol.cfg_read, b));
            r[a] = WH_CR32(b); break;
        case 3: { uint32_t v = imm ? b : (b < 16 ? r[b] : 0);
            if (!imm) REG(b);
            if (a > 0xffc || (a & 3)) { *code = pc - 1; { st = WIFI_BAD_OFFSET; goto out; } }
            POLICY(wifi_cfg_allowed(pol.cfg_write, a));
            WH_CW32(a, v); break; }
        case 4: REG(a); OFF(b, 4); r[a] = WH_R32(b); break;
        case 5: REG(a); OFF(b, 2); r[a] = WH_R16(b); break;
        case 6: case 7: { if (!imm) REG(b);
            uint32_t v = imm ? b : r[b];
            if (base == 6) { OFF(a, 4); POLICY(SINK_OK(a, v)); WH_W32(a, v); }
            else { OFF(a, 2); POLICY(NO_SINK(a)); WH_W16(a, (uint16_t)v); }
            break; }
        case 8: case 10: { REG(a); REG(b); uint32_t off = r[b] + c;
            if (base == 8) { OFF(off, 4); r[a] = WH_R32(off); }
            else { OFF(off, 2); r[a] = WH_R16(off); }
            break; }
        case 9: case 11: { REG(a); if (!imm) REG(c);
            uint32_t off = r[a] + b, v = imm ? c : r[c];
            if (base == 9) { OFF(off, 4); POLICY(SINK_OK(off, v)); WH_W32(off, v); }
            else { OFF(off, 2); POLICY(NO_SINK(off)); WH_W16(off, (uint16_t)v); }
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
            case 10: r[a] = v ? r[a] / v : 0; break;
            case 11: { int32_t x = (int32_t)r[a], y = (int32_t)v;
                r[a] = (y == 0) ? 0 : (x == INT32_MIN && y == -1) ? (uint32_t)x : (uint32_t)(x / y);
                break; }
            case 12: r[a] = v ? r[a] % v : r[a]; break;
            case 13: { int32_t x = (int32_t)r[a], y = (int32_t)v;
                r[a] = (y == 0) ? (uint32_t)x : (x == INT32_MIN && y == -1) ? 0 : (uint32_t)(x % y);
                break; }
            case 14: { uint32_t k = v >= 31 ? 31 : v;
                r[a] = (r[a] & 0x80000000u) ? ~((~r[a]) >> k) : r[a] >> k; break; }
            default: *code = pc - 1; { st = WIFI_BAD_OPCODE; goto out; }
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
            case 4: t = (int32_t)x < (int32_t)v; break;
            case 5: t = (int32_t)x >= (int32_t)v; break;
            default: *code = pc - 1; { st = WIFI_BAD_OPCODE; goto out; }
            }
            if (t) pc = c;
            break; }
        case 14: pc = a; break;
        case 15: WH_DELAY(a); break;
        case 16: { if (!imm) REG(b); WH_PRINT(a, imm ? b : r[b]); break; }
        case 17: { if (b > blob_len || c > (blob_len - b) / 4 || (b & 3)) {
                *code = pc - 1; { st = WIFI_BAD_BLOB; goto out; } }
            OFF(a, 4);
            POLICY(NO_SINK(a));
            for (uint32_t i = 0; i < c; ++i)
                WH_W32(a, wifi_le32(blob + b + 4 * i));
            break; }
        case 18: { REG(a); REG(b);
            uint64_t off = (uint64_t)c + (uint64_t)r[b] * 4;
            if ((c & 3) || off + 4 > blob_len) { *code = pc - 1; { st = WIFI_BAD_BLOB; goto out; } }
            r[a] = wifi_le32(blob + off); break; }
        case 19: if (sp == WIFI_STACK_DEPTH) { *code = pc - 1; { st = WIFI_STACK; goto out; } }
            stack[sp++] = pc; pc = a; break;
        case 20: if (sp == 0) { *code = pc - 1; { st = WIFI_STACK; goto out; } }
            pc = stack[--sp]; break;
        case 21: { REG(a); REG(b);
            uint64_t at = (uint64_t)r[b] + c;
            if (at + sub > WIFI_SCRATCH_BYTES || (sub != 1 && sub != 2 && sub != 4)) {
                *code = pc - 1; { st = WIFI_BAD_MEM; goto out; } }
            uint32_t v = 0;
            for (uint32_t i = 0; i < sub; ++i) v |= (uint32_t)S[at + i] << (8 * i);
            r[a] = v; break; }
        case 22: { REG(a); if (!imm) REG(c);
            uint64_t at = (uint64_t)r[a] + b;
            uint32_t v = imm ? c : r[c];
            if (at + sub > WIFI_SCRATCH_BYTES || (sub != 1 && sub != 2 && sub != 4)) {
                *code = pc - 1; { st = WIFI_BAD_MEM; goto out; } }
            for (uint32_t i = 0; i < sub; ++i) S[at + i] = (uint8_t)(v >> (8 * i));
            break; }
        case 23: case 24: { REG(b); REG(c); OFF(a, 4);
            if (base == 24) POLICY(NO_SINK(a));
            uint64_t at = r[b], n = r[c];
            if (at + 4 * n > WIFI_SCRATCH_BYTES) { *code = pc - 1; { st = WIFI_BAD_MEM; goto out; } }
            for (uint64_t i = 0; i < n; ++i) {
                volatile uint8_t *p = S + at + 4 * i;
                if (base == 23) {
                    uint32_t v = WH_R32(a);
                    p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8);
                    p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);
                } else {
                    WH_W32(a, (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
                              ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24));
                }
            }
            break; }
        case 25: REG(a);
            if (b > WIFI_SCRATCH_BYTES) { *code = pc - 1; { st = WIFI_BAD_MEM; goto out; } }
            POLICY(pol.dma);
            r[a] = WH_PHYS(b); break;
        case 26: if (a > 0xffc || (a & 3)) { *code = pc - 1; { st = WIFI_BAD_OFFSET; goto out; } }
            POLICY(a == 4 && !(b & ~pol.cmd_clear) && !(c & ~pol.cmd_set));
            WH_CW32(a, (WH_CR32(a) & ~b) | c); break;
        case 28: REG(a); OFF(b, 1); r[a] = WH_R8(b); break;
        case 29: { if (!imm) REG(b);
            uint32_t v = imm ? b : r[b];
            OFF(a, 1); POLICY(NO_SINK(a)); WH_W8(a, (uint8_t)v); break; }
        case 27: { if (!imm) REG(a);
            *code = imm ? a : r[a]; st = WIFI_YIELD; goto out; }
        default: *code = pc - 1; { st = WIFI_BAD_OPCODE; goto out; }
        }
#undef REG
#undef OFF
#undef POLICY
#undef SINK_OK
#undef NO_SINK
    }
    *code = pc;
    st = WIFI_STEP_LIMIT;
out:
    vm->sp = sp;
    vm->pc = pc;
    return st;
}

/* Start and run `image` to completion (programs that never yield); a yield
   ends the run with WIFI_YIELD. */
static inline int wifi_exec(const uint8_t *image, uint32_t image_len,
                            const struct wifi_hooks *h, uint64_t max_steps,
                            uint32_t *code) {
    static struct wifi_vm vm;
    if (wifi_start(&vm, image, image_len))
        return WIFI_BAD_IMAGE;
    return wifi_resume(&vm, h, max_steps, code);
}

#endif
