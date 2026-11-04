/* Law boot_text_parse_complete: for every geometry the Lean selector leanos_boot_text_surface accepts, in a
   well-formed Multiboot2 information buffer -- the fixed header (total size, reserved 0), up to two other tags
   (any type but 0 and 8, any size from 8 to 64 bytes, any contents), one EGA framebuffer tag (type 8, any size
   from 32 to 64 bytes, any bytes beyond the fields the parser reads), the end tag (type 0, size 8), each at
   8-byte alignment, with the total size exactly the end of the end tag -- passed with its exact length,
   boot_text_parse returns 1 and writes exactly that geometry.
   Not claimed: buffers with more tags, or with bytes after the end tag (`available` larger than the total). */
#include <stdlib.h>
#include "quickproof.h"
#include "console_api.h"

static void put32(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8); p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);
}

static uint32_t round8(uint32_t size) { return (size + 7u) & ~7u; }

int main(void) {
    uint32_t pitch = nondet_u32(), width = nondet_u32(), height = nondet_u32();
    qp_assume(leanos_boot_text_surface(2, 16, 0xb8000u, pitch, width, height) == 1);
    uint32_t others = nondet_u32();
    qp_assume(others <= 2u);
    uint32_t type0 = nondet_u32(), size0 = nondet_u32(), type1 = nondet_u32(), size1 = nondet_u32();
    uint32_t fb_size = nondet_u32();
    qp_assume(type0 != 0u && type0 != 8u && 8u <= size0 && size0 <= 64u);
    qp_assume(type1 != 0u && type1 != 8u && 8u <= size1 && size1 <= 64u);
    qp_assume(32u <= fb_size && fb_size <= 64u);

    uint32_t total = 8u + (others >= 1u ? round8(size0) : 0u) + (others >= 2u ? round8(size1) : 0u) +
        round8(fb_size) + 8u;
    uint8_t *info = malloc(total);
    if (info == NULL)
        return 0;
    nondet_bytes(info, total);
    put32(info, total);
    put32(info + 4, 0);
    uint32_t offset = 8;
    if (others >= 1u) { put32(info + offset, type0); put32(info + offset + 4, size0); offset += round8(size0); }
    if (others >= 2u) { put32(info + offset, type1); put32(info + offset + 4, size1); offset += round8(size1); }
    put32(info + offset, 8u);
    put32(info + offset + 4, fb_size);
    put32(info + offset + 8, 0xb8000u);
    put32(info + offset + 12, 0);
    put32(info + offset + 16, pitch);
    put32(info + offset + 20, width);
    put32(info + offset + 24, height);
    info[offset + 28] = 16;
    info[offset + 29] = 2;
    offset += round8(fb_size);
    put32(info + offset, 0);
    put32(info + offset + 4, 8);

    struct boot_text_geometry g;
    qp_assert(console_parse(info, total, &g) == 1);
    qp_assert(g.kind == 2 && g.bits == 16 && g.address == 0xb8000u);
    qp_assert(g.pitch == pitch && g.width == width && g.height == height);
    free(info);
    return 0;
}
