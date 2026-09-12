#ifndef LEANOS_LAB_QOTOM_ROOTPORT_BME_ARM_H
#define LEANOS_LAB_QOTOM_ROOTPORT_BME_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-rootport-bme-window.h"
#include "qotom-rootport-bme.h"

/* The caller supplies trusted primitive callbacks, immutable firmware copies,
 * and views bound to the compiled identity-mapped boot arrays. Context storage
 * must be private and disjoint from those inputs and the aperture. This gate
 * binds the local checks; AP/firmware exclusion remains a separate assumption.
 * Every rejected rearm clears authority from a previously armed context. */
static inline int lab_rootport_bme_arm(struct lab_rootport_bme_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables, uint32_t count,
        uint64_t address, const struct pci_enumeration_header *header,
        const struct pci_express_observation *prior) {
    if (!window) return 0;
    window->armed = 0;
    window->leaf = 0;
    window->root = 0;
    window->window = 0;
    window->function = 0;
    if (!qotom_rootport_header_valid(header) || !qotom_rootport_sample_valid(prior)) return 0;
    if (!view || !window->controls || !window->invalidate ||
        !window->store16 || !window->fault ||
        !lab_ecam_firmware_matches(tables, count)) return 0;
    struct lab_ecam_controls before, after;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, view->root_address) ||
        !lab_ecam_root_matches(view, before.cr3, address) ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, view->root_address)) return 0;
    /* No page-table write or device read is performed while arming. */
    window->leaf = &view->pt[address / 4096u];
    window->root = view->root_address;
    window->window = address;
    window->function = header->function;
    window->armed = 1;
    return 1;
}
#endif
