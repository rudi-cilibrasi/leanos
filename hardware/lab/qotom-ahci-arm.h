#ifndef LEANOS_LAB_QOTOM_AHCI_ARM_H
#define LEANOS_LAB_QOTOM_AHCI_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-ahci-window.h"
#include "qotom-ahci-capabilities.h"

/* The caller supplies trusted primitive callbacks, immutable firmware copies,
 * and views bound to the compiled identity-mapped boot arrays. Context storage
 * must be private and disjoint from those inputs and the aperture. This gate
 * binds the local checks; AP/firmware exclusion remains a separate assumption.
 * Every rejected rearm clears authority from a previously armed context. */
static inline int lab_ahci_arm(struct lab_ahci_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables, uint32_t count,
        uint64_t address, const struct pci_enumeration_header *header) {
    if (!window) return 0;
    window->armed = 0;
    window->leaf = 0;
    window->root = 0;
    window->window = 0;
    if (!header || header->bus != 0 || header->device != 19 || header->function != 0 ||
        header->words[0] != UINT32_C(0x0f238086) || header->words[2] != UINT32_C(0x0106010e) ||
        (header->words[3] & UINT32_C(0x00ff0000)) || !(header->words[1] & 2) ||
        header->words[9] != QOTOM_AHCI_BAR) return 0;
    if (!view || !window->controls || !window->invalidate ||
        !window->load32 || !window->fault ||
        !lab_ecam_firmware_matches(tables, count)) return 0;
    struct lab_ecam_controls before, after;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, view->root_address) ||
        !lab_ecam_root_matches(view, before.cr3, address) ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, view->root_address)) return 0;
    /* root_matches excludes higher mappings and ECAM aliases. Also exclude
     * every present alias to the AHCI page, regardless of leaf permissions. */
    for (unsigned i = 0; i < 4096; ++i)
        if ((view->pt[i] & 1) &&
            (view->pt[i] & UINT64_C(0x000ffffffffff000)) == QOTOM_AHCI_BAR) return 0;
    /* No page-table write or device read is performed while arming. */
    window->leaf = &view->pt[address / 4096u];
    window->root = view->root_address;
    window->window = address;
    window->armed = 1;
    return 1;
}
#endif
