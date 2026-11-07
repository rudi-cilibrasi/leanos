/* Shim for LeanOS's generated build/boundary-abi/boundary-abi.h: the three exports include/madt_generated_admission.h
   calls, with the prototypes the generated header gives them (LeanOS/BootTopology.lean). */
#ifndef LEANOS_BOUNDARY_ABI_H
#define LEANOS_BOUNDARY_ABI_H
#include <stdint.h>
uint64_t leanos_boot_machine_madt_entry_stream_byte_step_query(uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t);
uint64_t leanos_boot_machine_madt_envelope_byte_step_query(uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
uint64_t leanos_boot_machine_topology_admission_result_query(uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
#endif
