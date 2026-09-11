#ifndef LEANOS_PCI_AF_OBSERVATION_H
#define LEANOS_PCI_AF_OBSERVATION_H
#include "pci-capabilities.h"

/* This observer has no write path and makes no reset/drain decision. The
 * caller supplies the immutable header and its successfully collected list,
 * owns serialized configuration access, and keeps all inputs nonaliasing. */
enum pci_af_status {
    PCI_AF_OK, PCI_AF_NOT_PRESENT, PCI_AF_ARGUMENT, PCI_AF_LIST_CHANGED,
    PCI_AF_COLLECTION_FAILED, PCI_AF_READ_FAILED, PCI_AF_SHAPE, PCI_AF_ABSENT
};
struct pci_af_observation {
    enum pci_af_status status;
    uint8_t offset;
    uint32_t raw_control_status;
};

/* Refresh identity/list before reading control/status. At most 53 reads:
 * four initial header checks, 48 list slots, and one payload dword. The two
 * low bytes contain AF control/status; the upper bytes are retained without
 * interpretation. Header/list agreement does not prove an atomic snapshot. */
static inline struct pci_af_observation pci_observe_af(
        pci_enumeration_read read, void *context,
        const struct pci_enumeration_header *initial,
        const struct pci_capability_snapshot *previous) {
    struct pci_af_observation out = {PCI_AF_ARGUMENT, 0, 0};
    if (!read || !initial || !previous || previous->count > PCI_CAPABILITY_CAPACITY)
        return out;
    struct pci_capability_snapshot fresh;
    struct pci_capability_result result = pci_collect_capabilities(read, context, initial, &fresh);
    if (result.status != PCI_CAPABILITY_OK) {
        out.status = PCI_AF_COLLECTION_FAILED; return out;
    }
    if (fresh.count != previous->count) { out.status = PCI_AF_LIST_CHANGED; return out; }
    uint32_t selected = PCI_CAPABILITY_CAPACITY;
    for (uint32_t i = 0; i < fresh.count; ++i) {
        if (fresh.headers[i].offset != previous->headers[i].offset ||
            fresh.headers[i].raw != previous->headers[i].raw) {
            out.status = PCI_AF_LIST_CHANGED; return out;
        }
        if ((fresh.headers[i].raw & 255) == 0x13) {
            if (selected != PCI_CAPABILITY_CAPACITY) {out.status = PCI_AF_SHAPE; return out;}
            selected = i;
        }
    }
    if (selected == PCI_CAPABILITY_CAPACITY) {out.status = PCI_AF_NOT_PRESENT; return out;}
    const struct pci_capability_header *af = &fresh.headers[selected];
    /* Require the six-byte standard structure, both support bits, and no
     * reserved capability bits. Keep the following dword inside 256 bytes. */
    if ((af->raw >> 16) != 0x0306 || af->offset > 248) {
        out.status = PCI_AF_SHAPE; return out;
    }
    /* A second list header cannot overlap the control/status bytes. */
    for (uint32_t i = 0; i < fresh.count; ++i)
        if (fresh.headers[i].offset == af->offset + 4) {
            out.status = PCI_AF_SHAPE; return out;
        }
    uint32_t raw;
    if (!read(context, initial->bus, initial->device, initial->function,
              (uint8_t)(af->offset + 4), &raw)) {
        out.status = PCI_AF_READ_FAILED; return out;
    }
    if (raw == UINT32_MAX) {out.status = PCI_AF_ABSENT; return out;}
    out.status = PCI_AF_OK;
    out.offset = af->offset;
    out.raw_control_status = raw;
    return out;
}
#endif
