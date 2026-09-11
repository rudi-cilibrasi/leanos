#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
#include <string.h>
#define LEANOS_BOUNDARY_ABI_OBJECTS
#include "boundary-abi.h"
#include "../build/native-inventory/cases.h"
extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_QotomNativePCIInventory(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);
static int decimal_word(const char *text, uint64_t *value) {
    if (!*text || (text[0] == '0' && text[1])) return 0;
    uint64_t parsed = 0;
    for (; *text; ++text) {
        if (*text < '0' || *text > '9') return 0;
        unsigned digit = (unsigned)(*text - '0');
        if (parsed > (UINT64_MAX - digit) / 10) return 0;
        parsed = parsed * 10 + digit;
    }
    *value = parsed;
    return 1;
}

/* Bounded hosted transport for independently captured raw inventories.
 * Parsing is not admission: the generated model decides the result.
 */
static int replay_arguments(int argc, char **argv) {
    uint64_t count;
    if (argc < 3 || strcmp(argv[1], "inventory") ||
            !decimal_word(argv[2], &count) || count > 16 ||
            (uint64_t)(argc - 3) != count * 19) return 2;
    uint64_t input[16 * 19];
    for (unsigned i = 0; i < count * 19; ++i)
        if (!decimal_word(argv[i + 3], &input[i])) return 2;
    lean_object *words = lean_mk_empty_array_with_capacity(lean_box(count * 19));
    for (unsigned i = 0; i < count * 19; ++i)
        words = lean_array_push(words, lean_box_uint64(input[i]));
    printf("%" PRIu64 "\n", leanos_qotom_native_pci_inventory_check(count, words));
    return 0;
}

int main(int argc, char **argv) {
    lean_initialize();
    lean_object *init = initialize_leanos_LeanOS_QotomNativePCIInventory(1);
    if (lean_io_result_is_error(init)) {
        lean_io_result_show_error(init); lean_dec_ref(init); return 2;
    }
    lean_dec_ref(init); lean_io_mark_end_initialization();
    leanos_register_boundary_target("leanos_qotom_native_pci_inventory_check",
        (void *)(uintptr_t)&leanos_qotom_native_pci_inventory_check);
    leanos_register_boundary_target("leanos_qotom_pci_inventory_check",
        (void *)(uintptr_t)&leanos_qotom_pci_inventory_check);
    for (unsigned i=0; i<sizeof(native_cases)/sizeof(native_cases[0]); ++i) {
        lean_object *words = lean_mk_empty_array_with_capacity(lean_box(native_cases[i].size));
        for (unsigned j=0; j<native_cases[i].size; ++j)
            words = lean_array_push(words, lean_box_uint64(native_cases[i].words[j]));
        if (leanos_qotom_native_pci_inventory_check(native_cases[i].count, words) != native_cases[i].expected) {
            fprintf(stderr, "native inventory case failed: %s\n", native_cases[i].name); return 1;
        }
    }
    lean_object *words = lean_mk_empty_array_with_capacity(lean_box(304));
    for (unsigned j=0; j<304; ++j)
        words = lean_array_push(words, lean_box_uint64(native_cases[0].words[j]));
    if (leanos_qotom_pci_inventory_check(16, words) != 0x10000) return 1;
    if (argc > 1) return replay_arguments(argc, argv);
    puts("Hosted native Qotom inventory replay passed");
    return 0;
}
