#ifndef LEANOS_LAB_QOTOM_XHCI_SEMAPHORE_ARM_H
#define LEANOS_LAB_QOTOM_XHCI_SEMAPHORE_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-xhci-semaphore-window.h"
#include "qotom-xhci-legacy.h"

/* The caller supplies trusted primitive callbacks, immutable firmware copies,
 * and views bound to the compiled identity-mapped boot arrays. Context storage
 * must be private and disjoint from those inputs and the aperture. This gate
 * binds the local checks; AP/firmware exclusion remains a separate assumption.
 * The retained six-header list and seven capability samples bind the only
 * admitted DWORD request. The handoff helper must refresh them before writing.
 * Every rejected rearm clears authority from a previously armed context. */
static inline int lab_xhci_semaphore_arm(struct lab_xhci_semaphore_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables, uint32_t count,
        uint64_t address, const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,
        enum qotom_xhci_legacy_status status, const struct qotom_xhci_legacy *prior) {
    if (!window) return 0;
    window->armed = 0;
    window->leaf = 0;
    window->root = 0;
    window->window = 0;
    static const uint32_t expected_caps[7] = {
        0x01000080,0x07000820,0x84000054,0x0200000a,0x200077c1,0x3000,0x2000
    };
    static const struct qotom_xhci_ext_header expected_headers[6] = {
        {0x8000,0x02000802},{0x8020,0x03000802},{0x8040,0x00010cc1},
        {0x8070,0x0000fcc0},{0x8460,0x00010801},{0x8480,0x0005000a}
    };
    if (!caps || !prior || status != QOTOM_XHCI_LEGACY_OK || prior->count != 6 ||
        prior->legacy_offset != 0x8460 || prior->control_status != 0x2001) return 0;
    for (unsigned i=0;i<7;++i)
        if (caps->words[i] != expected_caps[i]) return 0;
    for (unsigned i=0;i<6;++i)
        if (prior->headers[i].offset != expected_headers[i].offset ||
            prior->headers[i].raw != expected_headers[i].raw) return 0;
    if (!header || header->bus != 0 || header->device != 20 || header->function != 0 ||
        header->words[0] != UINT32_C(0x0f358086) || header->words[2] != UINT32_C(0x0c03300e) ||
        (header->words[3] & UINT32_C(0x00ff0000)) || !(header->words[1] & 2) ||
        header->words[4] != (QOTOM_XHCI_BAR|4) || header->words[5]) return 0;
    if (!view || !window->controls || !window->invalidate ||
        !window->store32 || !window->fault ||
        !lab_ecam_firmware_matches(tables, count)) return 0;
    struct lab_ecam_controls before, after;
    if (!window->controls(window->opaque, &before) ||
        !lab_ecam_controls_match(&before, view->root_address) ||
        !lab_ecam_root_matches(view, before.cr3, address) ||
        !window->controls(window->opaque, &after) ||
        !lab_ecam_controls_match(&after, view->root_address)) return 0;
    /* root_matches excludes higher mappings and ECAM aliases. Also exclude
     * every present mapping into the 64-KiB XHCI resource, regardless of leaf permissions. */
    for (unsigned i = 0; i < 4096; ++i)
        if ((view->pt[i] & 1) &&
            (view->pt[i] & UINT64_C(0x000fffffffff0000)) == QOTOM_XHCI_BAR) return 0;
    /* No page-table write or device read is performed while arming. */
    window->leaf = &view->pt[address / 4096u];
    window->root = view->root_address;
    window->window = address;
    window->armed = 1;
    return 1;
}
#endif
