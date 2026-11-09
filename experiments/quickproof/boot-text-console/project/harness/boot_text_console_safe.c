/* Law boot_text_console_safe: for every Multiboot2 information buffer of up to 16 MiB (the kernel's
   BOOT_ACCESSIBLE_LIMIT) with any contents, passed with its exact length as `available`,
     - boot_text_parse (console_parse) reads only inside the buffer and returns 0 or 1; when it returns 1, the geometry it wrote
       is one the Lean selector leanos_boot_text_surface accepts, and its surface (height rows of pitch bytes)
       fits in the 32 KiB colour-text aperture;
   and then, with a window that is exactly that surface (height * pitch bytes, any prior contents),
     - boot_text_enable succeeds, and it and every later boot_text_putc (console_enable, console_putc) of any byte, for any number of bytes,
       write only inside the surface, and after each byte row < height and column <= width;
     - each byte other than CR and LF is displayed in the cell just before the cursor, as itself when it is
       printable ASCII (32..126) and as '?' otherwise, with attribute 0x07; CR returns to column 0 of the same
       row; LF goes to column 0 of the next row, or of the last row when the cursor was on it.
   The selector is linked as patch/lean_export_model.c, the model of LeanOS.BootTextConsole.checkRaw.
   Not claimed: termination (partial correctness), the physical address of the aperture, the bootloader's
   honesty, interrupt reentrancy (the `busy` flag), or the contents of the other cells (scrolling). */
#include <stdlib.h>
#include "quickproof.h"
#include "console_api.h"

int main(void) {
    size_t n = nondet_size();
    qp_assume(n <= 0x1000000u);
    uint8_t *info = malloc(n);
    if (info == NULL)
        return 0;
    nondet_bytes(info, n);

    struct boot_text_geometry g;
    int ok = console_parse(info, (uint32_t)n, &g);
    free(info);
    qp_assert(ok == 0 || ok == 1);
    if (ok == 0)
        return 0;
    qp_assert(leanos_boot_text_surface(g.kind, g.bits, g.address, g.pitch, g.width, g.height) == 1);
    qp_assert((uint64_t)g.height * g.pitch <= 32768u);

    uint32_t cells = g.height * (g.pitch / 2u);
    uint16_t *window = malloc((size_t)cells * sizeof(uint16_t));
    if (window == NULL)
        return 0;
    for (uint32_t i = 0; i < cells; ++i)
        window[i] = (uint16_t)nondet_u32();

    struct boot_text_console c;
    qp_assert(console_enable(&c, &g, window) == 1);
    while (nondet_u8() != 0) {
        uint8_t ch = nondet_u8();
        uint32_t row = c.row;
        console_putc(&c, ch);
        qp_assert(c.row < c.height);
        qp_assert(c.column <= c.width);
        if (ch == '\r') {
            qp_assert(c.column == 0 && c.row == row);
        } else if (ch == '\n') {
            qp_assert(c.column == 0 && c.row == (row + 1 < c.height ? row + 1 : c.height - 1));
        } else {
            uint16_t shown = (uint16_t)(0x0700u | (ch < 32 || ch > 126 ? '?' : ch));
            qp_assert(c.column >= 1);
            qp_assert(window[c.row * c.stride + c.column - 1] == shown);
        }
    }
    free(window);
    return 0;
}
