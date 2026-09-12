#ifndef LEANOS_LAB_QOTOM_REALTEK_STATE_WINDOW_H
#define LEANOS_LAB_QOTOM_REALTEK_STATE_WINDOW_H
#include "qotom-ecam-memory.h"
#include "qotom-realtek-state.h"

/* Bind the selected endpoint; no cross-endpoint reads through this context. */
static inline int lab_realtek_state_read_leaf(uint8_t bus,uint64_t address,uint8_t width,uint64_t *leaf) {
    uint64_t checked,bar=qotom_realtek_bar(bus);
    if (!leaf || !bar || address<bar || address>=bar+4096 ||
        !qotom_realtek_state_address(bus,(uint32_t)(address-bar),width,&checked) ||
        checked!=address) return 0;
    *leaf=bar|UINT64_C(0x8000000000000019); /* supervisor, RO, NX, PAT slot3 UC */
    return 1;
}

struct lab_realtek_state_window {
    volatile uint64_t *leaf;
    uint64_t root, window;
    unsigned armed;
    uint8_t bus;
    void *opaque;
    int (*controls)(void *, struct lab_ecam_controls *);
    void (*invalidate)(void *, uint64_t);
    int (*load)(void *, uint64_t, uint8_t, uint32_t *);
    void (*fault)(void *);
};

static __attribute__((noreturn)) inline void lab_realtek_state_window_fault(
        struct lab_realtek_state_window *window) {
    window->fault(window->opaque);
    __builtin_trap(); /* A terminal callback must never return. */
}

/* Caller arms only after firmware binding, active-root/ancestor validation and
 * alias exclusion. Callbacks are trusted native primitives, not device input.
 * No CR3 switch is performed. A native load fault is terminal; the fallible
 * load interface also permits hosted tests to exercise cleanup on rejection.
 * Context, output and private samples must not alias page-table storage.
 * Maskable interrupts remain disabled; firmware/AP exclusion is a separate
 * lab assumption, not something established by this transaction. */
static inline int lab_realtek_state_window_read(void *context, uint64_t address,
                                      uint8_t width, uint32_t *value) {
    struct lab_realtek_state_window *window = context;
    uint64_t mapped;
    struct lab_ecam_controls before, after;
    if (!window || !value || window->armed != 1 || !window->leaf ||
        !window->controls || !window->invalidate || !window->load || !window->fault ||
        !window->window || window->window >= UINT64_C(0x1000000) ||
        (window->window & 4095u) || !lab_realtek_state_read_leaf(window->bus, address, width, &mapped)) return 0;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, window->root)) return 0;
    const uint64_t saved = *window->leaf;
    const uint64_t ad = UINT64_C(0x60);
    const uint64_t expected = window->window | UINT64_C(0x8000000000000003);
    if ((saved & ~ad) != expected) return 0;
    *window->leaf = mapped;
    window->invalidate(window->opaque, window->window);
    uint32_t sampled = 0;
    const int loaded = window->load(window->opaque,
        window->window + (address & 4095u), width, &sampled);
    const uint64_t observed = *window->leaf;
    *window->leaf = saved;
    window->invalidate(window->opaque, window->window);
    if (*window->leaf != saved || (observed & ~UINT64_C(0x20)) != mapped ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, window->root))
        lab_realtek_state_window_fault(window);
    if (!loaded) return 0;
    *value = sampled;
    return 1;
}
#endif
