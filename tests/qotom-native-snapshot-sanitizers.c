#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "qotom-native-snapshot.c"
#include "capture.h"

static unsigned cases;
static void expect(uint64_t actual, uint64_t wanted) {
    if (actual != wanted) {
        fprintf(stderr, "snapshot case %u: %llu != %llu\n", cases,
            (unsigned long long)actual, (unsigned long long)wanted);
        exit(1);
    }
    ++cases;
}
int main(void) {
    struct pci_enumeration_snapshot input = captured;
    expect(qotom_native_snapshot_replay(0, &input), 0);
    expect(qotom_native_snapshot_replay(0, NULL), UINT64_C(1) << 32);
    struct qotom_native_inventory_result missing = qotom_check_native_inventory(
        PCI_ENUMERATION_OK, &input, NULL);
    expect(missing.status, QOTOM_NATIVE_INVENTORY_INVALID_ARGUMENT);
    for (unsigned status = 1; status <= 4; ++status)
        expect(qotom_native_snapshot_replay(status, &input), UINT64_C(2) << 32);
    for (unsigned count = 0; count <= 17; ++count) {
        input.count = count;
        expect(qotom_native_snapshot_replay(0, &input), count == 16 ? 0 : UINT64_C(3) << 32);
    }
    input.count = UINT32_MAX;
    expect(qotom_native_snapshot_replay(0, &input), UINT64_C(3) << 32);
    for (unsigned i = 0; i < 16; ++i) {
        for (unsigned address = 0; address < 3; ++address) {
            input = captured;
            if (address == 0) input.headers[i].bus = 255;
            if (address == 1) input.headers[i].device = 255;
            if (address == 2) input.headers[i].function = 255;
            expect(qotom_native_snapshot_replay(0, &input), (UINT64_C(4) << 32) | i);
        }
        const unsigned offsets[] = {0, 2, 3, 3};
        const uint32_t masks[] = {1, 1u << 8, 1u << 23, 2u << 16};
        for (unsigned j = 0; j < 4; ++j) {
            input = captured;
            input.headers[i].words[offsets[j]] ^= masks[j];
            expect(qotom_native_snapshot_replay(0, &input), (UINT64_C(4) << 32) | i);
        }
        if (i >= 6 && i < 10) {
            for (unsigned j = 0; j < 4; ++j) {
                input = captured;
                input.headers[i].words[j == 3 ? 15 : 6] ^= 1u << (j == 3 ? 16 : j * 8);
                expect(qotom_native_snapshot_replay(0, &input), (UINT64_C(4) << 32) | i);
            }
        }
    }
    input = captured;
    expect(qotom_native_collect_replay(&input, 0), 0);
    expect(qotom_native_collect_replay(&input, 1), UINT64_C(2) << 32);
    expect(memcmp(&input, &captured, sizeof input) == 0, 1);
    input.count = 15;
    expect(qotom_native_collect_replay(&input, 0), UINT64_C(3) << 32);
    printf("PASS native snapshot C loop: %u cases\n", cases);
    return 0;
}
