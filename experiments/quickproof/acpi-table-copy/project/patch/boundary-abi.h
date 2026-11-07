/* Shim for LeanOS's generated build/boundary-abi/boundary-abi.h: the two exports include/acpi_table_copy.h calls,
   with the prototypes the generated header gives them (LeanOS/BootTopology.lean). */
#ifndef LEANOS_BOUNDARY_ABI_H
#define LEANOS_BOUNDARY_ABI_H
#include <stdint.h>
uint64_t leanos_boot_machine_acpi_copy_sequence_step_query(uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
uint64_t leanos_boot_machine_acpi_copy_stream_step_query(uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
#endif
