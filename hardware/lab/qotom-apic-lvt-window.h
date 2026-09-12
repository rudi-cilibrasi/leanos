#ifndef LEANOS_LAB_QOTOM_APIC_LVT_WINDOW_H
#define LEANOS_LAB_QOTOM_APIC_LVT_WINDOW_H
#include <stddef.h>
#include <stdint.h>
#include "qotom-ecam-memory.h"

#define QOTOM_LOCAL_APIC_BASE UINT64_C(0xfee00000)
#define QOTOM_IA32_APIC_BASE UINT64_C(0xfee00900)
#define QOTOM_LVT_LINT0_OFFSET UINT64_C(0x350)
#define QOTOM_LVT_LINT1_OFFSET UINT64_C(0x360)

struct lab_qotom_lvt_sample {
    uint32_t lint0_first, lint1_first, lint0_second, lint1_second;
};

struct lab_qotom_lvt_window {
    volatile uint64_t *leaf;
    uint64_t root, aperture;
    unsigned armed;
    void *opaque;
    int (*controls)(void *, struct lab_ecam_controls *);
    void (*invalidate)(void *, uint64_t);
    int (*load32)(void *, uint64_t, uint32_t *);
    void (*fault)(void *);
};

static __attribute__((noreturn)) inline void lab_qotom_lvt_fault(
        struct lab_qotom_lvt_window *window) {
    window->fault(window->opaque);
    __builtin_trap();
}

/* Arm only for the captured xAPIC base and a complete 16 MiB leaf table with
 * no present alias to the local-APIC frame. The borrowed aperture must still
 * be its exact supervisor writable NX identity leaf, apart from hardware A/D
 * bits. Rejected rearm clears all previously granted authority. */
static inline int lab_qotom_lvt_arm(struct lab_qotom_lvt_window *window,
        volatile uint64_t *page_table, size_t leaf_count,
        uint64_t root, uint64_t aperture, uint64_t apic_base) {
    if (!window) return 0;
    window->armed = 0;
    window->leaf = NULL;
    window->root = 0;
    window->aperture = 0;
    if (!page_table || leaf_count != 4096u ||
        apic_base != QOTOM_IA32_APIC_BASE || !root || root >= UINT64_C(0x1000000) ||
        (root & 4095u) || !aperture || aperture >= UINT64_C(0x1000000) ||
        (aperture & 4095u) || !window->controls || !window->invalidate ||
        !window->load32 || !window->fault)
        return 0;
    struct lab_ecam_controls before, after;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, root)) return 0;
    const size_t aperture_page = (size_t)(aperture / 4096u);
    const uint64_t ad = UINT64_C(0x60);
    const uint64_t expected = aperture | UINT64_C(0x8000000000000003);
    if ((page_table[aperture_page] & ~ad) != expected) return 0;
    for (size_t page = 0; page < leaf_count; ++page)
        if ((page_table[page] & 1u) &&
            (page_table[page] & UINT64_C(0x000ffffffffff000)) == QOTOM_LOCAL_APIC_BASE)
            return 0;
    if (!window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, root)) return 0;
    window->leaf = &page_table[aperture_page];
    window->root = root;
    window->aperture = aperture;
    window->armed = 1;
    return 1;
}

/* Map the xAPIC page read-only, supervisor, NX and PAT-slot-3 UC. Read only
 * LVT LINT0/LINT1 twice, restore the exact old leaf, invalidate both changes,
 * and publish no partial sample. A changed mapping or CPU-control envelope is
 * terminal after restoration. Firmware, SMM and other processors remain an
 * explicit lab assumption; repeated raw values are observation, not proof.
 * Context and output storage are trusted private kernel objects disjoint from
 * the page tables and aperture. A native load fault is terminal. */
static inline int lab_qotom_lvt_read(struct lab_qotom_lvt_window *window,
                                    struct lab_qotom_lvt_sample *sample) {
    if (sample) *sample = (struct lab_qotom_lvt_sample){0,0,0,0};
    if (!window || !sample || window->armed != 1 || !window->leaf ||
        !window->controls || !window->invalidate || !window->load32 ||
        !window->fault || !window->root || !window->aperture)
        return 0;
    struct lab_ecam_controls before, after;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, window->root)) return 0;
    const uint64_t saved = *window->leaf;
    const uint64_t ad = UINT64_C(0x60);
    const uint64_t expected = window->aperture | UINT64_C(0x8000000000000003);
    const uint64_t mapped = QOTOM_LOCAL_APIC_BASE | UINT64_C(0x8000000000000019);
    if ((saved & ~ad) != expected) return 0;
    *window->leaf = mapped;
    window->invalidate(window->opaque, window->aperture);
    struct lab_qotom_lvt_sample candidate = {0,0,0,0};
    int loaded = window->load32(window->opaque,
        window->aperture + QOTOM_LVT_LINT0_OFFSET, &candidate.lint0_first) &&
        window->load32(window->opaque,
        window->aperture + QOTOM_LVT_LINT1_OFFSET, &candidate.lint1_first) &&
        window->load32(window->opaque,
        window->aperture + QOTOM_LVT_LINT0_OFFSET, &candidate.lint0_second) &&
        window->load32(window->opaque,
        window->aperture + QOTOM_LVT_LINT1_OFFSET, &candidate.lint1_second);
    const uint64_t observed = *window->leaf;
    *window->leaf = saved;
    window->invalidate(window->opaque, window->aperture);
    if (*window->leaf != saved || (observed & ~UINT64_C(0x20)) != mapped ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, window->root))
        lab_qotom_lvt_fault(window);
    if (!loaded) return 0;
    *sample = candidate;
    return 1;
}
#endif
