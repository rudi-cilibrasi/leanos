#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t leanos_boot_full_projection_fixture_query(uint64_t, uint64_t);
extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);
extern lean_object *
initialize_leanos_LeanOS_BootMemoryMapFullProjectionABI(uint8_t);

static void expect(const char *name, uint64_t actual, uint64_t expected) {
    if (actual != expected) {
        fprintf(stderr, "%s: expected %llu, got %llu\n", name,
                (unsigned long long)expected, (unsigned long long)actual);
        exit(1);
    }
}

static lean_object *run_host(int argc, char **argv) {
    (void)argc;
    (void)argv;
    const uint64_t rich_projection[] = {
        /* ABI, status, error, bytes, counts, selected frame. */
        1, 1, 0, 176, 6, 4, 9, 5, 1,
        /* Every decoded entry: base, length, kind. */
        0, 57344, 1,
        16384, 4096, 2,
        20480, 4096, 2,
        24576, 4096, 3,
        57345, 4095, 1,
        0, 57344, 1,
        /* Canonical normalized regions: start, count, kind. */
        0, 4, 1,
        4, 3, 2,
        7, 7, 1,
        14, 1, 2,
        /* Checked intervals: identity, first, count, lifetime. */
        1, 0, 1, 1,
        2, 3, 7, 1,
        3, 3, 1, 1,
        4, 4, 1, 1,
        5, 5, 1, 1,
        6, 8, 1, 1,
        7, 9, 1, 1,
        8, 6, 2, 1,
        9, 10, 2, 2,
        /* Reservation-overlaid regions: start, count, kind. */
        0, 1, 2,
        1, 2, 1,
        3, 9, 2,
        12, 2, 1,
        14, 1, 2,
    };
    const size_t word_count =
        sizeof(rich_projection) / sizeof(rich_projection[0]);

    for (size_t word = 0; word < word_count; ++word)
        expect("complete rich projection",
               leanos_boot_full_projection_fixture_query(0, word),
               rich_projection[word]);
    expect("complete rich projection terminator",
           leanos_boot_full_projection_fixture_query(0, word_count), 0);

    /* Reversing overlapping entries changes only the raw-entry witness order. */
    expect("reversed raw second entry base",
           leanos_boot_full_projection_fixture_query(1, 12), 57345);
    for (uint64_t word = 27; word < word_count; ++word)
        expect("order-independent full model projection",
               leanos_boot_full_projection_fixture_query(1, word),
               rich_projection[word]);

    expect("missing end rejected status",
           leanos_boot_full_projection_fixture_query(2, 1), 2);
    expect("missing end decoder error",
           leanos_boot_full_projection_fixture_query(2, 2), 111);
    expect("missing end exposes no projection",
           leanos_boot_full_projection_fixture_query(2, 8), 0);

    expect("address overflow rejected status",
           leanos_boot_full_projection_fixture_query(3, 1), 2);
    expect("address overflow model error",
           leanos_boot_full_projection_fixture_query(3, 2), 120);
    expect("address overflow exposes no projection",
           leanos_boot_full_projection_fixture_query(3, 8), 0);

    expect("mutated claim rejected status",
           leanos_boot_full_projection_fixture_query(4, 1), 2);
    expect("mutated claim exact error",
           leanos_boot_full_projection_fixture_query(4, 2), 401);
    expect("mutated claim exposes no selected frame",
           leanos_boot_full_projection_fixture_query(4, 8), 0);

    expect("maximum entry bound accepted",
           leanos_boot_full_projection_fixture_query(5, 1), 1);
    expect("maximum entry count retained",
           leanos_boot_full_projection_fixture_query(5, 4), 256);
    expect("maximum entry allocation selected",
           leanos_boot_full_projection_fixture_query(5, 8), 1);

    expect("truncated buffer rejected status",
           leanos_boot_full_projection_fixture_query(6, 1), 2);
    expect("truncated buffer decoder error",
           leanos_boot_full_projection_fixture_query(6, 2), 106);
    expect("truncated buffer exposes no projection",
           leanos_boot_full_projection_fixture_query(6, 8), 0);

    puts("NEGATIVE missing-end status=2 error=111 projection=none");
    puts("NEGATIVE truncated status=2 error=106 projection=none");
    puts("NEGATIVE address-overflow status=2 error=120 projection=none");
    puts("NEGATIVE output-mutation status=2 error=401 projection=none");
    puts("Hosted generated-C full boot-memory projection replay passed");
    return lean_io_result_mk_ok(lean_box(0));
}

int main(int argc, char **argv) {
    argv = lean_setup_args(argc, argv);
    lean_initialize();
    lean_object *result =
        initialize_leanos_LeanOS_BootMemoryMapFullProjectionABI(1);
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
