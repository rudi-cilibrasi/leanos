#ifndef LEANOS_LAB_QOTOM_ECAM_FIRMWARE_H
#define LEANOS_LAB_QOTOM_ECAM_FIRMWARE_H
#include <stdint.h>

struct lab_ecam_firmware_table {
    uint64_t address;
    const uint8_t *bytes;
    uint32_t length;
};

/* Generated from the manifest-verified native root/FADT/DSDT capture. */
#include "qotom-ecam-firmware-inputs.h"

/* Lab-only equality gate, not an AML interpreter or platform admission.
 * Callers supply complete immutable validated copies in root/children/DSDT
 * order, with readable storage for every claimed length. Equality binds the
 * reviewed static PDRC declaration and MCFG to these particular bytes. */
static inline int lab_ecam_firmware_matches(
        const struct lab_ecam_firmware_table *tables, uint32_t count) {
    if (!tables || count != LAB_ECAM_FIRMWARE_TABLE_COUNT) return 0;
    for (uint32_t i = 0; i < count; ++i) {
        const struct lab_ecam_firmware_table *expected = &lab_ecam_expected_tables[i];
        if (!tables[i].bytes || tables[i].address != expected->address ||
            tables[i].length != expected->length) return 0;
        for (uint32_t j = 0; j < expected->length; ++j)
            if (tables[i].bytes[j] != expected->bytes[j]) return 0;
    }
    return 1;
}
#endif
