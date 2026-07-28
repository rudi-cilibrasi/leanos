#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t leanos_boot_handoff_fixture_query(uint64_t, uint64_t);
extern uint64_t leanos_boot_handoff_query(uint64_t, uint64_t, lean_object *, uint64_t);
extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_BootMemoryMapDecoderABI(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);
#define REGISTER_BOUNDARY(symbol) \
    leanos_register_boundary_target(#symbol, (void *)(uintptr_t)&symbol)

static void expect(const char *name, uint64_t actual, uint64_t expected) {
    printf("boot-handoff-result %s %llu\n", name,
           (unsigned long long)actual);
    if (actual != expected) {
        fprintf(stderr, "%s: expected %llu, got %llu\n", name,
                (unsigned long long)expected, (unsigned long long)actual);
        exit(1);
    }
}

static lean_object *run_host(int argc, char **argv) {
    (void)argc;
    (void)argv;
    REGISTER_BOUNDARY(leanos_boot_handoff_query);
    REGISTER_BOUNDARY(leanos_boot_handoff_fixture_query);
    const uint64_t expected[] = {
        1, 1, 96, 2, 3,
        0x1000, 0x4000, 1,
        0x2000, 0x1000, 2,
        1, 1, 1,
        2, 1, 2,
        3, 2, 1
    };
    const char *const fields[] = {
        "abi-version", "status", "total-bytes", "entry-count", "region-count",
        "entry-0-base", "entry-0-length", "entry-0-kind",
        "entry-1-base", "entry-1-length", "entry-1-kind",
        "region-0-start", "region-0-count", "region-0-kind",
        "region-1-start", "region-1-count", "region-1-kind",
        "region-2-start", "region-2-count", "region-2-kind",
    };
    char name[96];
    lean_object *empty = lean_mk_empty_byte_array(lean_box(0));
    expect("production-empty-buffer.abi-version",
           leanos_boot_handoff_query(0, 0, empty, 0), 1);
    lean_dec(empty);

    for (size_t word = 0; word < sizeof(expected) / sizeof(expected[0]); ++word) {
        snprintf(name, sizeof(name), "accepted.%s", fields[word]);
        expect(name, leanos_boot_handoff_fixture_query(0, word), expected[word]);
    }
    expect("accepted.out-of-range", leanos_boot_handoff_fixture_query(0, 20), 0);

    expect("reversed.status", leanos_boot_handoff_fixture_query(1, 1), 1);
    expect("reversed.entry-0-kind", leanos_boot_handoff_fixture_query(1, 7), 2);
    expect("reversed.entry-1-kind", leanos_boot_handoff_fixture_query(1, 10), 1);
    for (uint64_t word = 11; word < 20; ++word) {
        snprintf(name, sizeof(name), "reversed.%s", fields[word]);
        expect(name, leanos_boot_handoff_fixture_query(1, word), expected[word]);
    }

    expect("truncated.status", leanos_boot_handoff_fixture_query(2, 1), 2);
    expect("truncated.typed-error", leanos_boot_handoff_fixture_query(2, 2), 6);
    for (uint64_t word = 0; word < 20; ++word) {
        snprintf(name, sizeof(name), "padding.%s", fields[word]);
        expect(name, leanos_boot_handoff_fixture_query(3, word), expected[word]);
    }

    puts("Hosted generated-C handoff projection replay passed");
    return lean_io_result_mk_ok(lean_box(0));
}

int main(int argc, char **argv) {
    argv = lean_setup_args(argc, argv);
    lean_initialize();
    lean_object *result =
        initialize_leanos_LeanOS_BootMemoryMapDecoderABI(1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(result)) {
        lean_dec(result);
        lean_init_task_manager();
        result = lean_run_main(&run_host, argc, argv);
    }
    lean_finalize_task_manager();
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        lean_dec(result);
        return 1;
    }
    lean_dec(result);
    return 0;
}
