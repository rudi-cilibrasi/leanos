#ifndef LEANOS_LAB_QOTOM_XHCI_EXT_ARM_H
#define LEANOS_LAB_QOTOM_XHCI_EXT_ARM_H
#include "qotom-xhci-arm.h"
#include "qotom-xhci-ext-window.h"

/* Bind the seven physical samples retained in qotom-native-xhci-20260911.
 * Private staging reuses firmware/root/alias checks without exporting the
 * capability reader's authority. Arming performs no device access. The bounded
 * collector must refresh these samples before following any extended link.
 * Inputs must be immutable and disjoint from context/page tables/aperture;
 * callbacks are trusted. Firmware/AP exclusion remains a separate assumption.
 * Failed rearm revokes all previously granted authority. */
static inline int lab_xhci_ext_arm(struct lab_xhci_ext_window *window,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables, uint32_t count,
        uint64_t address, const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps) {
    if (!window) return 0;
    window->armed = 0; window->leaf = 0; window->root = 0; window->window = 0;
    static const uint32_t expected[7] = {
        0x01000080, 0x07000820, 0x84000054, 0x0200000a,
        0x200077c1, 0x00003000, 0x00002000
    };
    if (!caps) return 0;
    for (unsigned i = 0; i < 7; ++i)
        if (caps->words[i] != expected[i]) return 0;
    struct lab_xhci_window staging = {.opaque=window->opaque,
        .controls=window->controls, .invalidate=window->invalidate,
        .load32=window->load32, .fault=window->fault};
    if (!lab_xhci_arm(&staging, view, tables, count, address, header)) return 0;
    window->leaf=staging.leaf; window->root=staging.root;
    window->window=staging.window; window->armed=1;
    return 1;
}
#endif
