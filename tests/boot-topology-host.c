#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t leanos_boot_topology_query(lean_object *, uint64_t, uint64_t,
                                           uint64_t);
extern uint64_t leanos_boot_topology_fixture_query(uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_acpi_copy_budget_query(uint64_t, uint64_t,
                                                            uint64_t);
extern uint64_t leanos_boot_machine_acpi_copy_stream_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_acpi_copy_sequence_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_madt_envelope_byte_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t);
extern uint64_t leanos_boot_machine_madt_local_apic_byte_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_madt_irrelevant_record_byte_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t);
extern uint64_t leanos_boot_machine_madt_entry_stream_byte_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_topology_admission_result_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
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
  REGISTER_BOUNDARY(leanos_boot_machine_acpi_copy_budget_query);
  REGISTER_BOUNDARY(leanos_boot_machine_acpi_copy_stream_step_query);
  REGISTER_BOUNDARY(leanos_boot_machine_acpi_copy_sequence_step_query);
  REGISTER_BOUNDARY(leanos_boot_machine_madt_envelope_byte_step_query);
  REGISTER_BOUNDARY(leanos_boot_machine_madt_local_apic_byte_step_query);
  REGISTER_BOUNDARY(
      leanos_boot_machine_madt_irrelevant_record_byte_step_query);
  REGISTER_BOUNDARY(
      leanos_boot_machine_madt_entry_stream_byte_step_query);
  REGISTER_BOUNDARY(leanos_boot_machine_topology_admission_result_query);

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

  expect("machine-copy-budget.exact.status",
         leanos_boot_machine_acpi_copy_budget_query(1048576 - 65536, 65536,
                                                     1),
         1);
  expect("machine-copy-budget.exact.next",
         leanos_boot_machine_acpi_copy_budget_query(1048576 - 65536, 65536,
                                                     3),
         1048576);
  expect("machine-copy-budget.exhausted.error",
         leanos_boot_machine_acpi_copy_budget_query(1048576 - 65528, 65536,
                                                     2),
         43);
  expect("machine-copy-budget.forged-cursor.error",
         leanos_boot_machine_acpi_copy_budget_query(1048577, 36, 2), 43);
  expect("machine-copy-budget.misaligned-cursor.error",
         leanos_boot_machine_acpi_copy_budget_query(1, 36, 2), 43);
  expect("machine-copy-budget.invalid-length.error",
         leanos_boot_machine_acpi_copy_budget_query(0, 65537, 2), 44);
  expect("machine-copy-stream.partial.next-copy",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 0, 0xf6000, 44, 0,
             UINT64_C(0x1122334455667788), 0, 5),
         0);
  expect("machine-copy-stream.terminal.next-byte",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 40, 0xf6000, 44, 40, UINT64_C(0xaabbccdd), 1, 4),
         44);
  expect("machine-copy-stream.terminal.next-copy",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 40, 0xf6000, 44, 40, UINT64_C(0xaabbccdd), 1, 5),
         48);
  expect("machine-copy-stream.forged-terminal.error",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 0, 0xf6000, 44, 0, 0, 1, 2),
         47);
  expect("machine-copy-stream.truncated-final-chunk.error",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 32, 0xf6000, 44, 32, 0, 1, 2),
         47);
  expect("machine-copy-stream.missing-final-marker.error",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 40, 0xf6000, 44, 40, 0, 0, 2),
         47);
  expect("machine-copy-stream.reordered-address.error",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 0, 0xf7000, 44, 0, 0, 0, 2),
         45);
  expect("machine-copy-stream.unaligned-physical-address.error",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6004, 0, 0xf6004, 44, 0,
             UINT64_C(0x1122334455667788), 0, 2),
         0);
  expect("machine-copy-stream.reordered-byte.error",
         leanos_boot_machine_acpi_copy_stream_step_query(
             0, 0xf6000, 8, 0xf6000, 44, 16, 0, 0, 2),
         46);
  expect("machine-copy-sequence.exact-terminal.next-ordinal",
         leanos_boot_machine_acpi_copy_sequence_step_query(1, 2, 1, 1, 1, 3),
         2);
  expect("machine-copy-sequence.duplicate-ordinal.error",
         leanos_boot_machine_acpi_copy_sequence_step_query(1, 2, 0, 1, 1, 2),
         48);
  expect("machine-copy-sequence.missing-ordinal.error",
         leanos_boot_machine_acpi_copy_sequence_step_query(1, 3, 2, 1, 0, 2),
         48);
  expect("machine-copy-sequence.forged-final.error",
         leanos_boot_machine_acpi_copy_sequence_step_query(0, 2, 0, 1, 1, 2),
         49);
  expect("machine-copy-sequence.missing-final.error",
         leanos_boot_machine_acpi_copy_sequence_step_query(1, 2, 1, 1, 0, 2),
         49);
  static const uint8_t complete_madt[] = {
      0x41, 0x50, 0x49, 0x43, 52, 0, 0, 0, 1, 165,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 8, 0, 0, 1, 0, 0, 0,
  };
  uint64_t madt_offset = 0, madt_length = 0, madt_checksum = 0;
  for (uint64_t byte = 0; byte < sizeof(complete_madt); ++byte) {
    const uint64_t terminal = byte + 1 == sizeof(complete_madt);
#define MADT_ENVELOPE_QUERY(word)                                              \
    leanos_boot_machine_madt_envelope_byte_step_query(                        \
        madt_offset, madt_length, madt_checksum, sizeof(complete_madt), byte,  \
        complete_madt[byte], terminal, (word))
    expect("machine-madt-envelope.step.error", MADT_ENVELOPE_QUERY(2), 0);
    expect("machine-madt-envelope.step.status", MADT_ENVELOPE_QUERY(1),
           terminal ? 3 : 1);
    const uint64_t next_madt_offset = MADT_ENVELOPE_QUERY(3);
    const uint64_t next_madt_length = MADT_ENVELOPE_QUERY(4);
    const uint64_t next_madt_checksum = MADT_ENVELOPE_QUERY(5);
    madt_offset = next_madt_offset;
    madt_length = next_madt_length;
    madt_checksum = next_madt_checksum;
#undef MADT_ENVELOPE_QUERY
  }
  expect("machine-madt-envelope.complete.offset", madt_offset,
         sizeof(complete_madt));
  expect("machine-madt-envelope.complete.length", madt_length,
         sizeof(complete_madt));
  expect("machine-madt-envelope.complete.checksum", madt_checksum, 0);
  expect("machine-madt-envelope.bad-signature.error",
         leanos_boot_machine_madt_envelope_byte_step_query(
             0, 0, 0, sizeof(complete_madt), 0, 0x58, 0, 2),
         56);
  expect("machine-madt-envelope.early-terminal.error",
         leanos_boot_machine_madt_envelope_byte_step_query(
             8, sizeof(complete_madt), 0, sizeof(complete_madt), 8, 0, 1, 2),
         59);
  static const uint8_t local_apic[] = {0, 8, 0, 0, 1, 0, 0, 0};
  uint64_t record_offset = 0, record_length = 0, apic_id = 0, flags = 0;
  for (uint64_t byte = 0; byte < sizeof(local_apic); ++byte) {
    const uint64_t terminal = byte + 1 == sizeof(local_apic);
#define MADT_LOCAL_APIC_QUERY(word)                                            \
    leanos_boot_machine_madt_local_apic_byte_step_query(                      \
        44 + byte, record_offset, record_length, apic_id, flags, 44 + byte,   \
        local_apic[byte], terminal, (word))
    expect("machine-madt-local-apic.step.error",
           MADT_LOCAL_APIC_QUERY(2), 0);
    expect("machine-madt-local-apic.step.status",
           MADT_LOCAL_APIC_QUERY(1), terminal ? 3 : 1);
    const uint64_t next_record_offset = MADT_LOCAL_APIC_QUERY(3);
    const uint64_t next_record_length = MADT_LOCAL_APIC_QUERY(4);
    const uint64_t next_apic_id = MADT_LOCAL_APIC_QUERY(5);
    const uint64_t next_flags = MADT_LOCAL_APIC_QUERY(6);
#undef MADT_LOCAL_APIC_QUERY
    record_offset = next_record_offset;
    record_length = next_record_length;
    apic_id = next_apic_id;
    flags = next_flags;
  }
  expect("machine-madt-local-apic.complete.offset", record_offset, 8);
  expect("machine-madt-local-apic.complete.length", record_length, 8);
  expect("machine-madt-local-apic.complete.apic-id", apic_id, 0);
  expect("machine-madt-local-apic.complete.flags", flags, 1);
  expect("machine-madt-local-apic.x2apic.error",
         leanos_boot_machine_madt_local_apic_byte_step_query(
             44, 0, 0, 0, 0, 44, 9, 0, 2),
         61);
  expect("machine-madt-local-apic.online-capable.error",
         leanos_boot_machine_madt_local_apic_byte_step_query(
             51, 7, 8, 0, 3, 51, 0, 1, 2),
         64);
  static const uint8_t io_apic[] = {1, 12, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  uint64_t irrelevant_offset = 0, irrelevant_kind = 0,
           irrelevant_length = 0;
  for (uint64_t byte = 0; byte < sizeof(io_apic); ++byte) {
    const uint64_t terminal = byte + 1 == sizeof(io_apic);
#define MADT_IRRELEVANT_QUERY(word)                                           \
    leanos_boot_machine_madt_irrelevant_record_byte_step_query(              \
        52 + byte, irrelevant_offset, irrelevant_kind, irrelevant_length,    \
        52 + byte, io_apic[byte], terminal, (word))
    expect("machine-madt-irrelevant.step.error",
           MADT_IRRELEVANT_QUERY(2), 0);
    expect("machine-madt-irrelevant.step.status",
           MADT_IRRELEVANT_QUERY(1), terminal ? 3 : 1);
    const uint64_t next_irrelevant_offset = MADT_IRRELEVANT_QUERY(3);
    const uint64_t next_irrelevant_kind = MADT_IRRELEVANT_QUERY(4);
    const uint64_t next_irrelevant_length = MADT_IRRELEVANT_QUERY(5);
#undef MADT_IRRELEVANT_QUERY
    irrelevant_offset = next_irrelevant_offset;
    irrelevant_kind = next_irrelevant_kind;
    irrelevant_length = next_irrelevant_length;
  }
  expect("machine-madt-irrelevant.complete.offset", irrelevant_offset, 12);
  expect("machine-madt-irrelevant.complete.kind", irrelevant_kind, 1);
  expect("machine-madt-irrelevant.complete.length", irrelevant_length, 12);
  expect("machine-madt-irrelevant.x2apic.error",
         leanos_boot_machine_madt_irrelevant_record_byte_step_query(
             52, 0, 0, 0, 52, 9, 0, 2),
         66);
  uint64_t stream_offset = 44, stream_record_offset = 0,
           stream_kind = 0, stream_length = 0, stream_apic_id = 0,
           stream_flags = 0, stream_enabled = 0, stream_admitted = 256,
           stream_seen0 = 0, stream_seen1 = 0, stream_seen2 = 0,
           stream_seen3 = 0;
  for (uint64_t byte = 44; byte < sizeof(complete_madt); ++byte) {
#define MADT_ENTRY_STREAM_QUERY(word)                                        \
    leanos_boot_machine_madt_entry_stream_byte_step_query(                  \
        stream_offset, stream_record_offset, stream_kind, stream_length,    \
        stream_apic_id, stream_flags, stream_enabled, stream_admitted,      \
        stream_seen0, stream_seen1, stream_seen2, stream_seen3,             \
        sizeof(complete_madt), 0, byte, complete_madt[byte], (word))
    const uint64_t terminal = byte + 1 == sizeof(complete_madt);
    expect("machine-madt-entry-stream.step.error",
           MADT_ENTRY_STREAM_QUERY(2), 0);
    expect("machine-madt-entry-stream.step.status",
           MADT_ENTRY_STREAM_QUERY(1), terminal ? 3 : 1);
    const uint64_t next_stream_offset = MADT_ENTRY_STREAM_QUERY(3);
    const uint64_t next_stream_record_offset = MADT_ENTRY_STREAM_QUERY(4);
    const uint64_t next_stream_kind = MADT_ENTRY_STREAM_QUERY(5);
    const uint64_t next_stream_length = MADT_ENTRY_STREAM_QUERY(6);
    const uint64_t next_stream_apic_id = MADT_ENTRY_STREAM_QUERY(7);
    const uint64_t next_stream_flags = MADT_ENTRY_STREAM_QUERY(8);
    const uint64_t next_stream_enabled = MADT_ENTRY_STREAM_QUERY(9);
    const uint64_t next_stream_admitted = MADT_ENTRY_STREAM_QUERY(10);
    const uint64_t next_stream_seen0 = MADT_ENTRY_STREAM_QUERY(11);
    const uint64_t next_stream_seen1 = MADT_ENTRY_STREAM_QUERY(12);
    const uint64_t next_stream_seen2 = MADT_ENTRY_STREAM_QUERY(13);
    const uint64_t next_stream_seen3 = MADT_ENTRY_STREAM_QUERY(14);
#undef MADT_ENTRY_STREAM_QUERY
    stream_offset = next_stream_offset;
    stream_record_offset = next_stream_record_offset;
    stream_kind = next_stream_kind;
    stream_length = next_stream_length;
    stream_apic_id = next_stream_apic_id;
    stream_flags = next_stream_flags;
    stream_enabled = next_stream_enabled;
    stream_admitted = next_stream_admitted;
    stream_seen0 = next_stream_seen0;
    stream_seen1 = next_stream_seen1;
    stream_seen2 = next_stream_seen2;
    stream_seen3 = next_stream_seen3;
  }
  expect("machine-madt-entry-stream.complete.offset", stream_offset,
         sizeof(complete_madt));
  expect("machine-madt-entry-stream.complete.enabled", stream_enabled, 1);
  expect("machine-madt-entry-stream.complete.admitted", stream_admitted, 0);
  expect("machine-madt-entry-stream.complete.seen0", stream_seen0, 1);
  expect("machine-madt-entry-stream.x2apic.error",
         leanos_boot_machine_madt_entry_stream_byte_step_query(
             44, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0, 52, 0, 44, 9, 2),
         70);
  expect("machine-admission.exact.status",
         leanos_boot_machine_topology_admission_result_query(
             2, 0xf5c00, 0xf5c00, 2, 2, 1, 1, 0, 0, 0, 1),
         1);
  expect("machine-admission.exact.apic-id",
         leanos_boot_machine_topology_admission_result_query(
             2, 0xf5c00, 0xf5c00, 2, 2, 1, 1, 0, 0, 0, 3),
         0);
  expect("machine-admission.incomplete-copy.error",
         leanos_boot_machine_topology_admission_result_query(
             2, 0xf5c00, 0xf5c00, 2, 1, 1, 1, 0, 0, 0, 2),
         51);
  expect("machine-admission.duplicate-madt.error",
         leanos_boot_machine_topology_admission_result_query(
             2, 0xf5c00, 0xf5c00, 2, 2, 2, 1, 0, 0, 0, 2),
         52);
  expect("machine-admission.forged-executing-apic.error",
         leanos_boot_machine_topology_admission_result_query(
             2, 0xf5c00, 0xf5c00, 2, 2, 1, 1, 0, 0, 1, 2),
         54);

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
