#ifndef LEANOS_LAB_QOTOM_REALTEK_STATE_ARM_H
#define LEANOS_LAB_QOTOM_REALTEK_STATE_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-realtek-state-window.h"
#include "qotom-realtek-state.h"

/* The caller supplies trusted primitive callbacks, immutable firmware copies,
 * and views bound to the compiled identity-mapped boot arrays. Context storage
 * must be private and disjoint from those inputs and the aperture. This gate
 * binds the local checks; upstream routing must be refreshed by the native
 * collector before MMIO. AP/firmware exclusion remains a separate assumption.
 * Every rejected rearm clears authority from a previously armed context. */
static inline int lab_realtek_state_arm(struct lab_realtek_state_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables, uint32_t count,
        uint64_t address, const struct pci_enumeration_header *header) {
    if (!window) return 0;
    window->armed = 0;
    window->leaf = 0;
    window->root = 0;
    window->window = 0;
    window->bus = 0;
    if (!qotom_realtek_header_valid(header)) return 0;
    if (!view || !window->controls || !window->invalidate ||
        !window->load || !window->fault ||
        !lab_ecam_firmware_matches(tables, count)) return 0;
    struct lab_ecam_controls before, after;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, view->root_address) ||
        !lab_ecam_root_matches(view, before.cr3, address) ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, view->root_address)) return 0;
    /* Exclude all five pages of both memory resources for the selected
     * endpoint, including BAR4 although this observer never reads it. */
    const uint64_t base=qotom_realtek_bar(header->bus)-UINT64_C(0x4000);
    for (unsigned i=0;i<4096;++i) {
        uint64_t physical=view->pt[i]&UINT64_C(0x000ffffffffff000);
        if ((view->pt[i]&1) && physical>=base && physical<base+UINT64_C(0x5000)) return 0;
    }
    /* No page-table write or device read is performed while arming. */
    window->leaf = &view->pt[address / 4096u];
    window->root = view->root_address;
    window->window = address;
    window->bus = header->bus;
    window->armed = 1;
    return 1;
}
#endif
