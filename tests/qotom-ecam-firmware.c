#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "qotom-ecam-firmware.h"

int main(void) {
    struct lab_ecam_firmware_table observed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    unsigned bytes_checked = 0;
    for (uint32_t i = 0; i < LAB_ECAM_FIRMWARE_TABLE_COUNT; ++i) {
        observed[i] = lab_ecam_expected_tables[i];
        uint8_t *copy = malloc(observed[i].length);
        assert(copy);
        memcpy(copy, observed[i].bytes, observed[i].length);
        observed[i].bytes = copy;
    }
    assert(lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT));
    assert(!lab_ecam_firmware_matches(0, LAB_ECAM_FIRMWARE_TABLE_COUNT));
    assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT - 1));
    assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT + 1));
    assert(!lab_ecam_firmware_matches(observed, UINT32_MAX));
    for (uint32_t i = 0; i < LAB_ECAM_FIRMWARE_TABLE_COUNT; ++i) {
        struct lab_ecam_firmware_table saved = observed[i];
        observed[i].address ^= UINT64_C(0x100000000);
        assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT));
        observed[i] = saved;
        observed[i].length--;
        assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT));
        observed[i] = saved;
        observed[i].length = UINT32_MAX;
        assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT));
        observed[i] = saved;
        observed[i].bytes = 0;
        assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT));
        observed[i] = saved;
        uint8_t *copy = (uint8_t *)observed[i].bytes;
        for (uint32_t j = 0; j < saved.length; ++j) {
            copy[j] ^= 1;
            assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT));
            copy[j] ^= 1;
            ++bytes_checked;
        }
    }
    struct lab_ecam_firmware_table first = observed[0];
    observed[0] = observed[1];
    observed[1] = first;
    assert(!lab_ecam_firmware_matches(observed, LAB_ECAM_FIRMWARE_TABLE_COUNT));
    for (uint32_t i = 0; i < LAB_ECAM_FIRMWARE_TABLE_COUNT; ++i)
        free((void *)observed[i].bytes);
    printf("Qotom firmware gate: %u single-byte mutations and extent/order rejections PASS\n", bytes_checked);
}
