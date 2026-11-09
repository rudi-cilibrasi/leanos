/* Shim for LeanOS's generated build/boundary-abi/boundary-abi.h: the five exports include/boot_handoff_decode.h calls,
   with the prototypes the generated header gives them (LeanOS/BootMemoryMapStreaming.lean and
   LeanOS/BootMemoryMapStreamAuthority.lean). */
#ifndef LEANOS_BOUNDARY_ABI_H
#define LEANOS_BOUNDARY_ABI_H
#include <stdint.h>
uint64_t leanos_boot_handoff_stream_init(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t);
uint64_t leanos_boot_handoff_stream_step(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
uint64_t leanos_boot_decode_init_v5(uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t);
uint64_t leanos_boot_decode_step_v5(uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t);
uint64_t leanos_boot_projection_entry(uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
#endif
