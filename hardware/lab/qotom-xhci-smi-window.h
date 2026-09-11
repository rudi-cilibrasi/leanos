#ifndef LEANOS_LAB_QOTOM_XHCI_SMI_WINDOW_H
#define LEANOS_LAB_QOTOM_XHCI_SMI_WINDOW_H
#include "qotom-ecam-memory.h"

/* Only a zero DWORD at captured USBLEGCTLSTS (BAR + 0x8464) is admitted.
 * The handoff semaphore at +0x8460 and every nonzero value are rejected. */
struct lab_xhci_smi_window {
    volatile uint64_t *leaf;
    uint64_t root, window;
    unsigned armed;
    void *opaque;
    int (*controls)(void *, struct lab_ecam_controls *);
    void (*invalidate)(void *, uint64_t);
    int (*store32)(void *, uint64_t, uint32_t);
    void (*fault)(void *);
};

static __attribute__((noreturn)) inline void lab_xhci_smi_window_fault(
        struct lab_xhci_smi_window *window) {
    window->fault(window->opaque);
    __builtin_trap(); /* A terminal callback must never return. */
}

/* Caller arms after exact firmware/resource/root checks and alias exclusion.
 * A request consumes authority even when rejected. Trusted store32 must execute
 * exactly one dword store or report failure; failure may still have changed the
 * device. No rollback is possible. Native faults are terminal. Private context
 * must not alias page-table storage. Firmware/AP exclusion is an assumption.
 * Restore/invalidate and post-check controls before returning any store result.
 */
static inline int lab_xhci_smi_window_write(void *context, uint64_t address, uint32_t value) {
    struct lab_xhci_smi_window *window = context;
    if (!window) return 0;
    const unsigned armed = window->armed;
    window->armed = 0;
    const uint64_t mapped = UINT64_C(0x80000000d090801b); /* RW, NX, supervisor, UC */
    struct lab_ecam_controls before, after;
    if (armed != 1 || address != UINT64_C(0xd0908464) || value != UINT32_C(0) || !window->leaf ||
        !window->controls || !window->invalidate || !window->store32 || !window->fault ||
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
    const int stored = window->store32(window->opaque, window->window + 0x464, UINT32_C(0));
    const uint64_t observed = *window->leaf;
    *window->leaf = saved;
    window->invalidate(window->opaque, window->window);
    if (*window->leaf != saved || (observed & ~ad) != mapped ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, window->root))
        lab_xhci_smi_window_fault(window);
    return stored != 0;
}
#endif
