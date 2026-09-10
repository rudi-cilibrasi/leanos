#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include "../build/pci-header-capture/cases.h"

extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_PCIHeaderObservation(uint8_t);
extern uint64_t leanos_pci_header_observe(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);

static uint64_t observe(uint64_t field, const uint64_t *w) {
    return leanos_pci_header_observe(field, w[0], w[1], w[2], w[3], w[4],
        w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14],
        w[15], w[16], w[17], w[18], w[19]);
}

int main(void) {
    lean_initialize();
    lean_object *init = initialize_leanos_LeanOS_PCIHeaderObservation(1);
    if (lean_io_result_is_error(init)) {
        lean_io_result_show_error(init);
        lean_dec_ref(init);
        return 2;
    }
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    const size_t count = sizeof(pci_header_cases) / sizeof(pci_header_cases[0]);
    for (size_t i = 0; i < count; ++i) {
        const uint64_t *w = pci_header_cases[i];
        for (uint64_t field = 0; field < 20; ++field) {
            if (observe(field, w) != w[20 + field]) {
                fprintf(stderr, "PCI header case %zu field %llu differs\n", i,
                    (unsigned long long)field);
                return 1;
            }
        }
        if (observe(20, w) != 0x105 || observe(UINT64_MAX, w) != 0x105) return 1;
    }
    printf("Hosted PCI header replay passed (%zu cases, 22 fields each)\n", count);
    return 0;
}
