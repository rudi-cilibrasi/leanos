/* The code under test as one library unit: include/boot_text_console.h, unchanged.  Its functions are static,
 * so this unit gives the three the laws call (as kernel.c's initialize_early_text and serial_putc do)
 * external names for the harnesses.  Each wrapper only forwards its arguments. */
#include "boot_text_console.h"

int console_parse(const uint8_t *info, uint32_t available, struct boot_text_geometry *out) {
    return boot_text_parse(info, available, out);
}

int console_enable(struct boot_text_console *c, const struct boot_text_geometry *g, uint16_t *window) {
    return boot_text_enable(c, g, window);
}

void console_putc(struct boot_text_console *c, uint8_t ch) {
    boot_text_putc(c, ch);
}
