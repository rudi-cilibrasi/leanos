#ifndef LEANOS_PCI_ENUMERATION_H
#define LEANOS_PCI_ENUMERATION_H

#include <stdint.h>

/* One configuration segment, all 256 buses, 32 devices and eight functions.
 * No topology, function-zero or multifunction shortcut can hide a readable
 * function. This is enumeration only, not inventory or DMA admission.
 */
#define PCI_ENUMERATION_CAPACITY 16u
#define PCI_ENUMERATION_WORDS 16u

struct pci_enumeration_header {
    uint8_t bus, device, function;
    uint32_t words[PCI_ENUMERATION_WORDS];
};

struct pci_enumeration_snapshot {
    uint32_t count;
    struct pci_enumeration_header headers[PCI_ENUMERATION_CAPACITY];
};

enum pci_enumeration_status {
    PCI_ENUMERATION_OK,
    PCI_ENUMERATION_READ_FAILED,
    PCI_ENUMERATION_CAPACITY_EXCEEDED,
    PCI_ENUMERATION_INVALID_ARGUMENT
};

struct pci_enumeration_result {
    enum pci_enumeration_status status;
    uint8_t bus, device, function, offset;
};

/* Return nonzero only when the dword was read successfully. The caller owns
 * access serialization and the meaning of an all-ones vendor (absence).
 * This interface exposes no write operation and uses no allocator.
 */
typedef int (*pci_enumeration_read)(void *, uint8_t, uint8_t, uint8_t,
                                    uint8_t, uint32_t *);

static struct pci_enumeration_result pci_enumerate_segment(
        pci_enumeration_read read, void *context,
        struct pci_enumeration_snapshot *snapshot) {
    struct pci_enumeration_result result = {PCI_ENUMERATION_OK, 0, 0, 0, 0};
    uint32_t count = 0;
    if (snapshot) snapshot->count = 0;
    if (!read || !snapshot) {
        result.status = PCI_ENUMERATION_INVALID_ARGUMENT;
        return result;
    }
    for (unsigned bus = 0; bus < 256; ++bus) {
        for (unsigned device = 0; device < 32; ++device) {
            for (unsigned function = 0; function < 8; ++function) {
                uint32_t identity;
                result.bus = (uint8_t)bus;
                result.device = (uint8_t)device;
                result.function = (uint8_t)function;
                result.offset = 0;
                if (!read(context, result.bus, result.device, result.function,
                          0, &identity)) {
                    result.status = PCI_ENUMERATION_READ_FAILED;
                    return result;
                }
                if ((uint16_t)identity == UINT16_MAX) continue;
                if (count == PCI_ENUMERATION_CAPACITY) {
                    result.status = PCI_ENUMERATION_CAPACITY_EXCEEDED;
                    return result;
                }
                struct pci_enumeration_header *header = &snapshot->headers[count];
                header->bus = result.bus;
                header->device = result.device;
                header->function = result.function;
                header->words[0] = identity;
                for (unsigned word = 1; word < PCI_ENUMERATION_WORDS; ++word) {
                    result.offset = (uint8_t)(word * 4);
                    if (!read(context, result.bus, result.device, result.function,
                              result.offset, &header->words[word])) {
                        result.status = PCI_ENUMERATION_READ_FAILED;
                        return result;
                    }
                }
                ++count;
            }
        }
    }
    /* Publish a count only after the entire segment was scanned. On failure,
     * header storage may be partial and must not be consumed as a snapshot.
     */
    snapshot->count = count;
    result.bus = result.device = result.function = result.offset = 0;
    return result;
}

#endif
