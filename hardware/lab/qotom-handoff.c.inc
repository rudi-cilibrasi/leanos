/* Bounded initial-map observation, before allocation or device quarantine.
 * Reads each emitted byte once; does not claim an atomic firmware snapshot. */
#include "boot_handoff_capture.h"
static void lab_capture_handoff(uint32_t magic, uint32_t address) {
    const uint8_t *info = (const uint8_t *)(uintptr_t)address;
    uint32_t available = address < BOOT_ACCESSIBLE_LIMIT
        ? BOOT_ACCESSIBLE_LIMIT - address : 0;
    uint32_t length = boot_handoff_capture_length(magic, address, info, available);
    serial_puts("LEANOS-LAB/1 HANDOFF status="); serial_u64(length ? 0 : 1);
    serial_puts(" magic="); serial_u64(magic);
    serial_puts(" address="); serial_u64(address);
    serial_puts(" length="); serial_u64(length);
    serial_puts(" apic="); serial_u64(observe_executing_apic_id());
    serial_putc('\n');
    for (uint32_t offset = 0; offset < length; offset += 64u) {
        serial_puts("LEANOS-LAB/1 HANDOFF-DATA offset="); serial_u64(offset);
        serial_puts(" hex=");
        for (uint32_t i = offset; i < length && i < offset + 64u; ++i) {
            static const char digits[] = "0123456789abcdef";
            uint8_t value = info[i];
            serial_putc(digits[value >> 4]); serial_putc(digits[value & 15]);
        }
        serial_putc('\n');
    }
    serial_puts("LEANOS-LAB/1 HANDOFF-END\n");
}
