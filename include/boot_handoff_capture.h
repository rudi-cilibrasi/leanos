#ifndef LEANOS_BOOT_HANDOFF_CAPTURE_H
#define LEANOS_BOOT_HANDOFF_CAPTURE_H
#include <stdint.h>

/* Lab byte transport only: no tag interpretation or platform admission.
 * Caller supplies the readable extent corresponding to the physical address.
 * A rejected address must not cause even the size field to be read. */
static uint32_t boot_handoff_capture_length(uint32_t magic, uint32_t address,
                                           const uint8_t *info, uint32_t available) {
    if (magic != 0x36d76289u || (address & 7u) || address < 4096u ||
        address > 0x1000000u - 8u || available < 8u) return 0;
    uint32_t total = (uint32_t)info[0] | (uint32_t)info[1] << 8 |
                     (uint32_t)info[2] << 16 | (uint32_t)info[3] << 24;
    if (total < 16u || total > 65536u || (total & 7u) ||
        total > available || total > 0x1000000u - address) return 0;
    return total;
}
#endif
