#ifndef LEANOS_QOTOM_EHCI_CAPABILITIES_H
#define LEANOS_QOTOM_EHCI_CAPABILITIES_H
#include "pci-enumeration.h"

#define QOTOM_EHCI_BAR UINT64_C(0xd0915000)
typedef int (*qotom_ehci_mmio_read)(void *, uint64_t, uint32_t *);
struct qotom_ehci_capabilities { uint32_t capbase, structural, capability; };
enum qotom_ehci_status {
    QOTOM_EHCI_OK, QOTOM_EHCI_ARGUMENT, QOTOM_EHCI_HEADER,
    QOTOM_EHCI_CONFIG_READ, QOTOM_EHCI_DRIFT, QOTOM_EHCI_MMIO_READ,
    QOTOM_EHCI_ABSENT, QOTOM_EHCI_FORMAT
};

/* Address selection only, not permission to map or read MMIO. Caller must
 * establish fresh resource binding, UC/no-alias/root contracts and ownership
 * of the private mapping window before supplying the read callback. */
static inline int qotom_ehci_capability_address(uint32_t offset, uint64_t *out) {
    if (!out || (offset != 0 && offset != 4 && offset != 8)) return 0;
    *out = QOTOM_EHCI_BAR + offset;
    return 1;
}

/* Exactly five config checks precede at most three MMIO reads. Inputs remain
 * immutable, nonaliasing and serialized for the full operation. Header recheck
 * detects drift; it cannot provide atomicity or exclude firmware mutation.
 * Failure publishes zero fields, including failure on the final MMIO read. */
static inline enum qotom_ehci_status qotom_collect_ehci_capabilities(
        pci_enumeration_read config, void *config_context,
        qotom_ehci_mmio_read mmio, void *mmio_context,
        const struct pci_enumeration_header *initial,
        struct qotom_ehci_capabilities *out) {
    if (out) *out = (struct qotom_ehci_capabilities){0,0,0};
    if (!config || !mmio || !initial || !out) return QOTOM_EHCI_ARGUMENT;
    if (initial->bus != 0 || initial->device != 29 || initial->function != 0 ||
        initial->words[0] != UINT32_C(0x0f348086) ||
        initial->words[2] != UINT32_C(0x0c03200e) ||
        (initial->words[3] & UINT32_C(0x00ff0000)) ||
        !(initial->words[1] & 2) || initial->words[4] != QOTOM_EHCI_BAR)
        return QOTOM_EHCI_HEADER;
    const uint32_t masks[5] = {UINT32_MAX,2,UINT32_MAX,UINT32_C(0x00ff0000),UINT32_MAX};
    for (uint32_t i = 0; i < 5; ++i) {
        uint32_t raw;
        if (!config(config_context,0,29,0,(uint8_t)(i*4),&raw))
            return QOTOM_EHCI_CONFIG_READ;
        if ((raw & masks[i]) != (initial->words[i] & masks[i]))
            return QOTOM_EHCI_DRIFT;
    }
    uint32_t values[3];
    for (uint32_t i = 0; i < 3; ++i) {
        uint64_t address;
        if (!qotom_ehci_capability_address(i*4,&address)) return QOTOM_EHCI_ARGUMENT;
        if (!mmio(mmio_context,address,&values[i])) return QOTOM_EHCI_MMIO_READ;
        if (values[i] == UINT32_MAX) return QOTOM_EHCI_ABSENT;
    }
    /* Require EHCI 1.0 and an aligned non-overlapping operational base in the
     * same page. No operational read is performed. Preserve other raw fields. */
    uint32_t length = values[0] & 255;
    if ((values[0] >> 16) != 0x100 || (values[0] & 0xff00) ||
        length < 16 || (length & 3) || !(values[1] & 15)) return QOTOM_EHCI_FORMAT;
    *out = (struct qotom_ehci_capabilities){values[0],values[1],values[2]};
    return QOTOM_EHCI_OK;
}
#endif
