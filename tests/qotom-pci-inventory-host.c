#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <inttypes.h>
#include <string.h>
#include "../boot/pci-enumeration.h"
#define LEANOS_BOUNDARY_ABI_OBJECTS
#include "boundary-abi.h"
#include "../build/qotom-pci-inventory/cases.h"

extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_QotomPCIInventory(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);

struct collection_fixture {
    int missing, changed, rogue, fail;
    unsigned reads;
};

static int read_capture(void *context, uint8_t bus, uint8_t device,
                        uint8_t function, uint8_t offset, uint32_t *word) {
    struct collection_fixture *fixture = context;
    ++fixture->reads;
    if (fixture->fail && bus == 255 && device == 31 && function == 7) return 0;
    if (fixture->rogue && bus == 255 && device == 31 && function == 7) {
        *word = offset == 0 ? UINT32_C(0x12348086) : 0;
        return 1;
    }
    for (unsigned i = 0; i < 15; ++i) {
        const uint64_t *raw = &inventory_cases[0].words[i * 19];
        if (raw[0] == bus && raw[1] == device && raw[2] == function) {
            if ((int)i == fixture->missing) break;
            *word = (uint32_t)raw[3 + offset / 4];
            if ((int)i == fixture->changed && offset == 0) *word = UINT32_C(0x12348086);
            return 1;
        }
    }
    *word = UINT32_MAX;
    return 1;
}

/* This allocates hosted Lean objects. It is the tested collection-to-model
 * transport, not a freestanding adapter or hardware admission authority. */
static uint64_t check_collected(const struct pci_enumeration_snapshot *snapshot) {
    lean_object *words = lean_mk_empty_array_with_capacity(lean_box(snapshot->count * 19));
    for (unsigned i = 0; i < snapshot->count; ++i) {
        const struct pci_enumeration_header *h = &snapshot->headers[i];
        words = lean_array_push(words, lean_box_uint64(h->bus));
        words = lean_array_push(words, lean_box_uint64(h->device));
        words = lean_array_push(words, lean_box_uint64(h->function));
        for (unsigned j = 0; j < 16; ++j)
            words = lean_array_push(words, lean_box_uint64(h->words[j]));
    }
    return leanos_qotom_pci_inventory_check(snapshot->count, words);
}

static void test_collected_inventory(void) {
    struct pci_enumeration_snapshot snapshot;
    struct collection_fixture fixture = {-1, -1, 0, 0, 0};
    assert(pci_enumerate_segment(read_capture, &fixture, &snapshot).status == PCI_ENUMERATION_OK);
    assert(fixture.reads == 65761 && snapshot.count == 15 && check_collected(&snapshot) == 1);
    for (int i = 0; i < 15; ++i) {
        fixture = (struct collection_fixture){i, -1, 0, 0, 0};
        assert(pci_enumerate_segment(read_capture, &fixture, &snapshot).status == PCI_ENUMERATION_OK);
        assert(snapshot.count == 14 && check_collected(&snapshot) == UINT64_C(0x10000));
        fixture = (struct collection_fixture){-1, i, 0, 0, 0};
        assert(pci_enumerate_segment(read_capture, &fixture, &snapshot).status == PCI_ENUMERATION_OK);
        assert(check_collected(&snapshot) == UINT64_C(0x40000) + (unsigned)i);
    }
    fixture = (struct collection_fixture){-1, -1, 1, 0, 0};
    assert(pci_enumerate_segment(read_capture, &fixture, &snapshot).status == PCI_ENUMERATION_OK);
    assert(snapshot.count == 16 && check_collected(&snapshot) == UINT64_C(0x10000));
    fixture = (struct collection_fixture){-1, -1, 0, 1, 0};
    assert(pci_enumerate_segment(read_capture, &fixture, &snapshot).status == PCI_ENUMERATION_READ_FAILED);
    assert(snapshot.count == 0); /* Never pass a failed collection to admission. */
    puts("Collected PCI snapshots passed generated inventory admission and 32 negative cases");
}

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
            !decimal_word(argv[2], &count) || count > PCI_ENUMERATION_CAPACITY ||
            (uint64_t)(argc - 3) != count * 19) return 2;
    uint64_t input[PCI_ENUMERATION_CAPACITY * 19];
    for (unsigned i = 0; i < count * 19; ++i)
        if (!decimal_word(argv[i + 3], &input[i])) return 2;
    lean_object *words = lean_mk_empty_array_with_capacity(lean_box(count * 19));
    for (unsigned i = 0; i < count * 19; ++i)
        words = lean_array_push(words, lean_box_uint64(input[i]));
    printf("%" PRIu64 "\n", leanos_qotom_pci_inventory_check(count, words));
    return 0;
}

int main(int argc, char **argv) {
    lean_initialize();
    lean_object *init = initialize_leanos_LeanOS_QotomPCIInventory(1);
    if (lean_io_result_is_error(init)) {
        lean_io_result_show_error(init);
        lean_dec_ref(init);
        return 2;
    }
    lean_dec_ref(init);
    lean_io_mark_end_initialization();
    leanos_register_boundary_target("leanos_qotom_pci_inventory_check",
        (void *)(uintptr_t)&leanos_qotom_pci_inventory_check);
    size_t count = sizeof(inventory_cases) / sizeof(inventory_cases[0]);
    for (size_t i = 0; i < count; ++i) {
        lean_object *words = lean_mk_empty_array_with_capacity(lean_box(inventory_cases[i].size));
        for (size_t j = 0; j < inventory_cases[i].size; ++j)
            words = lean_array_push(words, lean_box_uint64(inventory_cases[i].words[j]));
        /* The exported function consumes this complete immutable array. */
        uint64_t actual = leanos_qotom_pci_inventory_check(inventory_cases[i].count, words);
        if (actual != inventory_cases[i].expected) {
            fprintf(stderr, "%s: got %llu expected %llu\n", inventory_cases[i].name,
                (unsigned long long)actual, (unsigned long long)inventory_cases[i].expected);
            return 1;
        }
    }
    if (argc > 1) return replay_arguments(argc, argv);
    printf("Hosted Qotom PCI inventory replay passed (%zu cases)\n", count);
    test_collected_inventory();
    return 0;
}
