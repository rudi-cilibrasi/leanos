#ifndef LEANOS_QOTOM_ECAM_READ_H
#define LEANOS_QOTOM_ECAM_READ_H

#include <stdint.h>

/* A decoded MCFG allocation is input, not authority to access MMIO. The
 * caller must bind it to the unique validated native MCFG and establish
 * resource ownership, effective UC mapping, alias and fault contracts. */
struct qotom_ecam_allocation {
    uint64_t base;
    uint16_t segment;
    uint8_t first_bus, last_bus;
};

/* Restrict this candidate to the captured segment-zero Qotom allocation and
 * conventional configuration dwords used by pci_enumerate_segment. MCFG base
 * addresses are relative to bus zero. No output is changed on rejection. */
static inline int qotom_ecam_dword_address(
        const struct qotom_ecam_allocation *allocation,
        uint32_t bus, uint32_t device, uint32_t function, uint32_t offset,
        uint64_t *address) {
    if (!allocation || !address || allocation->base != UINT64_C(0xe0000000) ||
        allocation->segment != 0 || allocation->first_bus != 0 ||
        allocation->last_bus != 255 || bus > 255 || device > 31 ||
        function > 7 || offset > 252 || (offset & 3u))
        return 0;
    *address = allocation->base + ((uint64_t)bus << 20) +
        ((uint64_t)device << 15) + ((uint64_t)function << 12) + offset;
    return 1;
}

/* The access callback implements one aligned dword read under an established
 * mapping contract. This interface supplies no mapping or write operation.
 * A false return must not publish a value; a hardware fault is terminal under
 * the caller's exception policy. */
typedef int (*qotom_ecam_access)(void *, uint64_t, uint32_t *);
struct qotom_ecam_reader {
    struct qotom_ecam_allocation allocation;
    qotom_ecam_access access;
    void *context;
};

/* Compatible with pci_enumeration_read. Keep the sample private until the
 * admitted access callback reports success. UINT32_MAX retains the collector's
 * existing absence semantics; it is not interpreted as an access failure. */
static inline int qotom_ecam_read(void *context, uint8_t bus, uint8_t device,
        uint8_t function, uint8_t offset, uint32_t *value) {
    const struct qotom_ecam_reader *reader = context;
    uint64_t address;
    if (!reader || !reader->access || !value ||
        !qotom_ecam_dword_address(&reader->allocation, bus, device, function,
                                 offset, &address))
        return 0;
    uint32_t sampled;
    if (!reader->access(reader->context, address, &sampled)) return 0;
    *value = sampled;
    return 1;
}

#endif
