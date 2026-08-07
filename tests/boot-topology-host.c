#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t leanos_boot_topology_query(lean_object *, uint64_t, uint64_t,
                                           uint64_t);
extern uint64_t leanos_boot_topology_fixture_query(uint64_t, uint64_t);
extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_BootTopology(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);
#define REGISTER_BOUNDARY(symbol)                                               \
  leanos_register_boundary_target(#symbol, (void *)(uintptr_t)&symbol)

static void expect(const char *field, uint64_t actual, uint64_t expected) {
  printf("topology-result %s %llu\n", field, (unsigned long long)actual);
  if (actual != expected) {
    fprintf(stderr, "topology replay first mismatch at %s: expected %llu, got "
                    "%llu\n",
            field, (unsigned long long)expected, (unsigned long long)actual);
    exit(1);
  }
}

static lean_object *run_host(int argc, char **argv) {
  (void)argc;
  (void)argv;
  REGISTER_BOUNDARY(leanos_boot_topology_query);
  REGISTER_BOUNDARY(leanos_boot_topology_fixture_query);

  static const uint64_t expected[][5] = {
      {1, 1, 0, 1, 0},   /* mixed q35 singleton */
      {1, 3, 7, 0, 0},   /* two enabled processors */
      {1, 3, 5, 0, 0},   /* disabled but online-capable processor */
      {1, 3, 4, 0, 0},   /* duplicate APIC ID */
      {1, 1, 255, 1, 0}, /* maximum byte APIC ID */
      {1, 2, 2, 0, 0},   /* truncated record */
      {1, 2, 4, 0, 0},   /* unsupported topology-bearing record */
      {1, 3, 8, 0, 0},   /* missing recorded BSP */
      {1, 3, 8, 0, 0},   /* attacker-mutated recorded BSP identity */
      {1, 3, 8, 0, 0},   /* attacker-mutated executing identity */
      {1, 2, 8, 0, 0},   /* invalid complete-table signature */
      {1, 2, 9, 0, 0},   /* complete-table declared-length mismatch */
      {1, 2, 11, 0, 0},  /* complete-table checksum mismatch */
      {1, 2, 6, 0, 0},   /* truncated fixed MADT header */
      {1, 1, 0, 1, 0},   /* authoritative root-to-admission success */
      {1, 2, 23, 0, 0},  /* conflicting old/new roots */
      {1, 2, 24, 0, 0},  /* selected root address mismatch */
      {1, 2, 26, 0, 0},  /* missing advertised-table translation */
      {1, 2, 27, 0, 0},  /* duplicate advertised-table translation */
      {1, 2, 28, 0, 0},  /* no translated MADT */
      {1, 2, 29, 0, 0},  /* multiple translated MADTs */
  };
  static const char *const fields[] = {"abi", "status", "detail", "enabled",
                                        "online-capable"};
  char name[96];
  const uint64_t fixture_count = sizeof(expected) / sizeof(expected[0]);
  for (uint64_t fixture = 0; fixture < fixture_count; ++fixture) {
    for (uint64_t word = 0; word < 5; ++word) {
      snprintf(name, sizeof(name), "fixture-%llu.%s",
               (unsigned long long)fixture, fields[word]);
      expect(name, leanos_boot_topology_fixture_query(fixture, word),
             expected[fixture][word]);
    }
  }
  expect("fixture-0.out-of-range", leanos_boot_topology_fixture_query(0, 5), 0);

  lean_object *empty = lean_mk_empty_byte_array(lean_box(0));
  /* The exported Lean function consumes its ByteArray argument. */
  expect("raw-empty.status", leanos_boot_topology_query(empty, 0, 0, 1), 3);
  puts("Hosted generated-C topology replay passed");
  return lean_io_result_mk_ok(lean_box(0));
}

int main(int argc, char **argv) {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  lean_object *result = initialize_leanos_LeanOS_BootTopology(1);
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
