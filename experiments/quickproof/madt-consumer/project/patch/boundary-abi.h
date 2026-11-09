/* Shim for LeanOS's generated build/boundary-abi/boundary-abi.h: the three exports include/qotom_bsp_consumer.h
   calls, with the prototypes the generated header gives them (LeanOS/QotomMadtStream.lean). */
#ifndef LEANOS_BOUNDARY_ABI_H
#define LEANOS_BOUNDARY_ABI_H
#include <stdint.h>
uint64_t leanos_qotom_madt_nmi_policy_query(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
uint64_t leanos_qotom_madt_stream_byte_step_query(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
uint64_t leanos_qotom_madt_stream_finish_query(uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
#endif
