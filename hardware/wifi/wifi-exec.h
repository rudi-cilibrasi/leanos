/* Image format, executor state and device hooks for Lean-authored device
   programs.

   The instruction set and its encoding are defined by
   LeanOS/Wifi/Bytecode.lean. This file parses an image (`wifi_image_header`,
   `wifi_start`) and declares the executor state and the device-effect hooks;
   it no longer contains an interpreter. Instructions are executed by the
   generated executor of wifi-gen-exec.h: `leanos_device_program_step`, the
   compiled `LeanOS.Wifi.Exec.step`, proved equal to `Sim.step` (issue #494,
   ADR 0020). It is shared by the FreeBSD userland development runner, the
   hosted fuzz and cross-check runners, the LeanOS lab kernel and the
   device-service kernel, which supply the effect hooks below. */
#ifndef LEANOS_WIFI_EXEC_H
#define LEANOS_WIFI_EXEC_H

#include <stdint.h>

#define WIFI_MAGIC 0x4649574cu
#define WIFI_WINDOW_BYTES 0x4000u        /* version-1 (Broadcom) window */
#define WIFI_WINDOW_MAX 0x10000u
#define WIFI_STACK_DEPTH 16
#define WIFI_SCRATCH_BYTES 262144u
#define WIFI_MAX_SINKS 8
#define WIFI_MAX_DESCS 16

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
   bus address (low) or zero (high) may touch them. Older images carry none.
   The descriptor map (Descriptor in Bytecode.lean, flags bit 1) names scratch
   regions of 64-bit pointer fields or TRBs that the device dereferences: a
   scratch store must leave every field in them zero or an in-scratch bus
   address (Sim.descOk), and FIFO input never lands in them. */
struct wifi_desc { uint32_t trb, start, count, stride; };
struct wifi_policy {
    uint32_t present, dma, window;
    uint64_t cfg_read, cfg_write;
    uint32_t cmd_clear, cmd_set;
    uint32_t sink_count, sinks[WIFI_MAX_SINKS];
    uint32_t desc_count;
    struct wifi_desc descs[WIFI_MAX_DESCS];
};

/* Descriptor.limit: one past the region's last byte (count >= 1). */
static inline uint64_t wifi_desc_limit(const struct wifi_desc *d) {
    return (uint64_t)d->start + (uint64_t)d->stride * (d->count - 1u) + (d->trb ? 16u : 8u);
}

/* The policy declares descriptor `d` (lab profile admission). */
static inline int wifi_has_desc(const struct wifi_policy *p, const struct wifi_desc *d) {
    for (uint32_t i = 0; i < p->desc_count; ++i)
        if (p->descs[i].trb == d->trb && p->descs[i].start == d->start &&
            p->descs[i].count == d->count && p->descs[i].stride == d->stride) return 1;
    return 0;
}

static inline int wifi_is_sink(const struct wifi_policy *p, uint32_t off) {
    for (uint32_t i = 0; i < p->sink_count; ++i)
        if (p->sinks[i] == off) return 1;
    return 0;
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
    pol->desc_count = 0;
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
    /* Windows come in 512-byte units: the q35 AHCI program's window is the
       host control registers and ports 0 and 1 only (issue #496). */
    if (t->window == 0 || t->window > WIFI_WINDOW_MAX || (t->window & 0x1ffu) ||
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
        if ((flags & ~3u) || t->window > pol->window || pol->sink_count > WIFI_MAX_SINKS ||
            image_len < 68u + 4u * pol->sink_count)
            return WIFI_BAD_IMAGE;
        for (uint32_t i = 0; i < pol->sink_count; ++i)
            pol->sinks[i] = wifi_le32(image + 68 + 4 * i);
        *header_len = 68 + 4 * pol->sink_count;
        if (flags & 2u) {
            /* Descriptor map (Policy.descWf): at most 16 regions of 1-4096
               entries, each inside scratch. */
            uint32_t at = *header_len;
            if (image_len < at + 4u) return WIFI_BAD_IMAGE;
            pol->desc_count = wifi_le32(image + at);
            if (pol->desc_count > WIFI_MAX_DESCS || image_len < at + 4u + 16u * pol->desc_count)
                return WIFI_BAD_IMAGE;
            for (uint32_t i = 0; i < pol->desc_count; ++i) {
                struct wifi_desc *d = &pol->descs[i];
                const uint8_t *e = image + at + 4 + 16 * i;
                d->trb = wifi_le32(e); d->start = wifi_le32(e + 4);
                d->count = wifi_le32(e + 8); d->stride = wifi_le32(e + 12);
                if (d->trb > 1u || d->count < 1u || d->count > 4096u ||
                    wifi_desc_limit(d) > WIFI_SCRATCH_BYTES)
                    return WIFI_BAD_IMAGE;
            }
            *header_len = at + 4 + 16 * pol->desc_count;
        }
    }
    return 0;
}

/* Resumable executor state. `wifi_start` parses an image and zeroes the
   registers and scratch; `wifi_gen_resume` (wifi-gen-exec.h) runs until the
   program halts, fails, faults, yields (opcode 27) or the step count reaches
   `step_limit`. After a yield, the next resume continues with the following
   instruction. */
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

#endif
