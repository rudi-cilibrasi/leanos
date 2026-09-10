#ifndef LEANOS_BOOT_TEXT_CONSOLE_H
#define LEANOS_BOOT_TEXT_CONSOLE_H
#include <stdint.h>

#include "boundary-abi.h"
struct boot_text_geometry {
    uint64_t address;
    uint32_t pitch, width, height;
    uint8_t kind, bits;
};
struct boot_text_console {
    volatile uint16_t *cells;
    uint32_t stride, width, height, row, column;
    volatile uint8_t enabled, busy;
};
static uint32_t boot_text_u32(const uint8_t *p) {
    return (uint32_t)p[0] | (uint32_t)p[1] << 8 |
           (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
}
/* Inspect a caller-owned bounded buffer, never the advertised surface. Accept
 * only after the whole aligned tag chain terminates; duplicate surfaces reject.
 * The caller separately validates the physical extent before reading the header. */
static int boot_text_parse(const uint8_t *info, uint32_t available,
                           struct boot_text_geometry *out) {
    volatile struct boot_text_geometry *cleared = out;
    cleared->address = 0;
    cleared->pitch = 0;
    cleared->width = 0;
    cleared->height = 0;
    cleared->kind = 0;
    cleared->bits = 0;
    if (available < 16) return 0;
    uint32_t total = boot_text_u32(info);
    if (total < 16 || total > available || total > 65536 || (total & 7) ||
        boot_text_u32(info + 4) != 0) return 0;
    uint32_t offset = 8;
    int seen = 0;
    while (offset <= total - 8) {
        const uint8_t *tag = info + offset;
        uint32_t type = boot_text_u32(tag), size = boot_text_u32(tag + 4);
        if (size < 8 || size > total - offset) return 0;
        uint32_t advance = (size + 7u) & ~7u;
        if (advance > total - offset) return 0;
        if (type == 0) {
            if (size != 8 || offset + advance != total || !seen) return 0;
            return leanos_boot_text_surface(out->kind, out->bits, out->address,
                                            out->pitch, out->width, out->height) == 1;
        }
        if (type == 8) {
            if (seen || size < 32) return 0;
            seen = 1;
            out->address = boot_text_u32(tag + 8) | (uint64_t)boot_text_u32(tag + 12) << 32;
            out->pitch = boot_text_u32(tag + 16);
            out->width = boot_text_u32(tag + 20);
            out->height = boot_text_u32(tag + 24);
            out->bits = tag[28];
            out->kind = tag[29];
        }
        offset += advance;
    }
    return 0;
}
static void boot_text_disable(struct boot_text_console *c) {
    c->enabled = 0;
}
/* window must name the already-owned initial text aperture. Host tests supply
 * an equally sized guarded buffer; production supplies only address 0xb8000. */
static int boot_text_enable(struct boot_text_console *c,
                            const struct boot_text_geometry *g,
                            volatile uint16_t *window) {
    boot_text_disable(c);
    if (leanos_boot_text_surface(g->kind, g->bits, g->address,
                                 g->pitch, g->width, g->height) != 1) return 0;
    c->cells = window;
    c->stride = g->pitch / 2;
    c->width = g->width;
    c->height = g->height;
    c->row = c->column = 0;
    c->busy = 1;
    for (uint32_t y = 0; y < c->height; ++y)
        for (uint32_t x = 0; x < c->width; ++x)
            c->cells[y * c->stride + x] = 0x0720;
    c->busy = 0;
    c->enabled = 1;
    return 1;
}
static void boot_text_line(struct boot_text_console *c) {
    c->column = 0;
    if (++c->row < c->height) return;
    for (uint32_t y = 1; y < c->height; ++y)
        for (uint32_t x = 0; x < c->width; ++x)
            c->cells[(y - 1) * c->stride + x] = c->cells[y * c->stride + x];
    c->row = c->height - 1;
    for (uint32_t x = 0; x < c->width; ++x)
        c->cells[c->row * c->stride + x] = 0x0720;
}
static void boot_text_putc(struct boot_text_console *c, uint8_t ch) {
    if (!c->enabled || c->busy) return;
    c->busy = 1;
    if (ch == '\r') c->column = 0;
    else if (ch == '\n') boot_text_line(c);
    else {
        /* Delay wrapping until the next printable byte so an exact-width
         * line followed by LF does not consume two screen rows. */
        if (c->column == c->width) boot_text_line(c);
        if (ch < 32 || ch > 126) ch = '?';
        c->cells[c->row * c->stride + c->column++] = (uint16_t)(0x0700u | ch);
    }
    c->busy = 0;
}
#endif
