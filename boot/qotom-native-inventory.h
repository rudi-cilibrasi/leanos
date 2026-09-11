#ifndef LEANOS_QOTOM_NATIVE_INVENTORY_H
#define LEANOS_QOTOM_NATIVE_INVENTORY_H
#include "pci-enumeration.h"

/* Bind this callback to the proved generated scalar header checker. Snapshot
 * storage must be private and immutable throughout the loop. A matching
 * inventory conveys no command-write, DMA, or CPL3 authority. */
typedef uint8_t (*qotom_native_header_check)(uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);

enum qotom_native_inventory_status {
    QOTOM_NATIVE_INVENTORY_MATCH,
    QOTOM_NATIVE_INVENTORY_INVALID_ARGUMENT,
    QOTOM_NATIVE_INVENTORY_SCAN_FAILED,
    QOTOM_NATIVE_INVENTORY_COUNT_REJECTED,
    QOTOM_NATIVE_INVENTORY_HEADER_REJECTED
};
struct qotom_native_inventory_result {
    enum qotom_native_inventory_status status;
    uint32_t index;
};

static struct qotom_native_inventory_result qotom_check_native_inventory(
    enum pci_enumeration_status scan_status,
    const struct pci_enumeration_snapshot *snapshot,
    qotom_native_header_check check) {
    struct qotom_native_inventory_result result = {
        QOTOM_NATIVE_INVENTORY_INVALID_ARGUMENT, 0};
    if (!snapshot || !check) return result;
    if (scan_status != PCI_ENUMERATION_OK) {
        result.status = QOTOM_NATIVE_INVENTORY_SCAN_FAILED;
        return result;
    }
    if (snapshot->count != 16) {
        result.status = QOTOM_NATIVE_INVENTORY_COUNT_REJECTED;
        return result;
    }
    for (uint32_t i = 0; i < 16; ++i) {
        const struct pci_enumeration_header *h = &snapshot->headers[i];
        const uint32_t *w = h->words;
        if (check(i, h->bus, h->device, h->function,
                  w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7],
                  w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]) != 1) {
            result.status = QOTOM_NATIVE_INVENTORY_HEADER_REJECTED;
            result.index = i;
            return result;
        }
    }
    result.status = QOTOM_NATIVE_INVENTORY_MATCH;
    return result;
}
#endif
