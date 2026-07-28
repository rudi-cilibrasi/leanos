#ifndef LEANOS_COMPOSITE_DISPATCHER_H
#define LEANOS_COMPOSITE_DISPATCHER_H

#include <stdint.h>

/*
 * Version-one scalar ABI for LeanOS.CompositeDispatcher.dispatch.
 *
 * Input words are ordered as state token, command tag, then arguments 0..3.
 * The result is one packed reply word.  All fields are logical uint64_t
 * values; there is no caller-owned buffer or byte-order-dependent structure.
 */
#define LEANOS_COMPOSITE_ABI_VERSION UINT64_C(1)
#define LEANOS_COMPOSITE_INPUT_WORDS 6U
#define LEANOS_COMPOSITE_RESULT_WORDS 1U

uint64_t leanos_composite_dispatch(
    uint64_t state,
    uint64_t command,
    uint64_t arg0,
    uint64_t arg1,
    uint64_t arg2,
    uint64_t arg3);

#endif
