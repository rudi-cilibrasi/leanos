#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#define LEANOS_BOUNDARY_ABI_OBJECTS
#include "boundary-abi.h"
#include "../build/qotom-quarantine-transition/cases.h"
#include "pci-command-executor-fixture.h"

extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_QotomPCIQuarantineTransition(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);

int main(void) {
    lean_initialize();
    lean_object *init = initialize_leanos_LeanOS_QotomPCIQuarantineTransition(1);
    if (lean_io_result_is_error(init)) {
        lean_io_result_show_error(init);
        lean_dec_ref(init);
        return 2;
    }
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    leanos_register_boundary_target("leanos_qotom_pci_quarantine_transition",
        (void *)(uintptr_t)&leanos_qotom_pci_quarantine_transition);
    test_command_executor();
    size_t count = sizeof(inventory_cases) / sizeof(inventory_cases[0]);
    for (size_t i = 0; i < count; ++i) {
        lean_object *words = lean_mk_empty_array_with_capacity(lean_box(inventory_cases[i].size));
        for (size_t j = 0; j < inventory_cases[i].size; ++j)
            words = lean_array_push(words, lean_box_uint64(inventory_cases[i].words[j]));
        /* The exported function consumes this complete immutable array. */
        uint64_t actual = leanos_qotom_pci_quarantine_transition(inventory_cases[i].count, words);
        if (actual != inventory_cases[i].expected) {
            fprintf(stderr, "%s: got %llu expected %llu\n", inventory_cases[i].name,
                (unsigned long long)actual, (unsigned long long)inventory_cases[i].expected);
            return 1;
        }
    }
    printf("Hosted Qotom quarantine transition replay passed (%zu cases)\n", count);
    return 0;
}
