/* The external names patch/console_unit.c gives the console's functions (see there). */
#ifndef LEANOS_CONSOLE_API_H
#define LEANOS_CONSOLE_API_H
#include "boot_text_console.h"
int console_parse(const uint8_t *info, uint32_t available, struct boot_text_geometry *out);
int console_enable(struct boot_text_console *c, const struct boot_text_geometry *g, uint16_t *window);
void console_putc(struct boot_text_console *c, uint8_t ch);
#endif
