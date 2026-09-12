#ifndef LEANOS_LAB_QOTOM_AHCI_BME_WINDOW_H
#define LEANOS_LAB_QOTOM_AHCI_BME_WINDOW_H
#include "qotom-ecam-memory.h"

/* Only the captured AHCI PCI Command word at ECAM 00:13.0 + 4.
 * This type cannot grant general ECAM writes or write adjacent PCI Status. */
struct lab_ahci_bme_window {
    volatile uint64_t *leaf;
    uint64_t root, window;
    unsigned armed;
    void *opaque;
    int (*controls)(void *, struct lab_ecam_controls *);
    void (*invalidate)(void *, uint64_t);
    int (*store16)(void *, uint64_t, uint16_t);
    void (*fault)(void *);
};

static __attribute__((noreturn)) inline void lab_ahci_bme_window_fault(
        struct lab_ahci_bme_window *window) {
    window->fault(window->opaque);
    __builtin_trap(); /* A terminal callback must never return. */
}

/* Caller arms after exact firmware/resource/root checks and alias exclusion.
 * A request consumes authority even when rejected. Trusted store16 must execute
 * exactly one word store or report failure; failure may still have changed the
 * device. No rollback is possible. Native faults are terminal. Private context
 * must not alias page-table storage. Firmware/AP exclusion is an assumption.
 * Restore/invalidate and post-check controls before returning any store result.
 */
static inline int lab_ahci_bme_window_write(void *context, uint8_t bus,
        uint8_t device, uint8_t function, uint8_t offset, uint16_t value) {
    struct lab_ahci_bme_window *window = context;
    if (!window) return 0;
    const unsigned armed = window->armed;
    window->armed = 0;
    const uint64_t mapped = UINT64_C(0x80000000e009801b); /* RW, NX, supervisor, UC */
    struct lab_ecam_controls before, after;
    if (armed != 1 || bus || device != 19 || function || offset != 4 || value != 0x3 || !window->leaf ||
        !window->controls || !window->invalidate || !window->store16 || !window->fault ||
        !window->window || window->window >= UINT64_C(0x1000000) ||
        (window->window & 4095u)) return 0;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, window->root)) return 0;
    const uint64_t saved = *window->leaf;
    const uint64_t ad = UINT64_C(0x60);
    const uint64_t expected = window->window | UINT64_C(0x8000000000000003);
    if ((saved & ~ad) != expected) return 0;
    *window->leaf = mapped;
    window->invalidate(window->opaque, window->window);
    const int stored = window->store16(window->opaque, window->window + 4, 0x3);
    const uint64_t observed = *window->leaf;
    *window->leaf = saved;
    window->invalidate(window->opaque, window->window);
    if (*window->leaf != saved || (observed & ~ad) != mapped ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, window->root))
        lab_ahci_bme_window_fault(window);
    return stored != 0;
}
#endif
