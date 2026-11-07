/* Shim for LeanOS's generated build/boundary-abi/boundary-abi.h: the six exports include/boot_frame_selection.h
   calls, with the prototypes the generated header gives them (LeanOS/BootMemoryMapStreamAuthority.lean). */
#ifndef LEANOS_BOUNDARY_ABI_H
#define LEANOS_BOUNDARY_ABI_H
#include <stdint.h>
uint64_t leanos_boot_authority_result(uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
uint64_t leanos_boot_consume_exact_projection(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
uint64_t leanos_boot_manifest_candidate(uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t);
uint64_t leanos_boot_projection_finish(uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
uint64_t leanos_boot_projection_free(uint64_t, uint64_t, uint64_t);
uint64_t leanos_boot_projection_manifest(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
#endif
