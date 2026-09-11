#ifndef LEANOS_ACPI_DSDT_ADDRESS_H
#define LEANOS_ACPI_DSDT_ADDRESS_H
#include <stdint.h>

/* Input must be an immutable, checksum-validated FADT selected uniquely from
 * the validated root. This helper selects an address, not access authority.
 * ACPI 1.0 revision 1 uses DSDT; revision 3 and later prefer nonzero X_DSDT.
 * The lab copy backend supports only physical addresses below 4 GiB. */
static inline int lab_fadt_dsdt_address(const uint8_t *bytes, uint32_t length,
                                      uint64_t *output) {
    if (!bytes || !output || length < 116u || length > 65536u ||
        bytes[0] != 'F' || bytes[1] != 'A' || bytes[2] != 'C' || bytes[3] != 'P')
        return 0;
    uint32_t declared = 0;
    uint64_t address = 0;
    for (uint32_t i = 0; i < 4; ++i) {
        declared |= (uint32_t)bytes[4 + i] << (8u * i);
        address |= (uint64_t)bytes[40 + i] << (8u * i);
    }
    if (declared != length || (bytes[8] != 1u && bytes[8] < 3u)) return 0;
    if (bytes[8] >= 3u) {
        if (length < 148u) return 0;
        uint64_t extended = 0;
        for (uint32_t i = 0; i < 8; ++i)
            extended |= (uint64_t)bytes[140 + i] << (8u * i);
        if (extended) address = extended;
    }
    if (!address || address > UINT64_C(0x100000000) - 36u) return 0;
    *output = address;
    return 1;
}
#endif
