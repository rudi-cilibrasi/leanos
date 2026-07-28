#ifndef LEANOS_COMPOSITE_DISPATCHER_H
#define LEANOS_COMPOSITE_DISPATCHER_H

#include <stdint.h>

/*
 * Version-one scalar ABI for LeanOS.CompositeDispatcher.dispatch.
 *
 * Input words are ordered as the canonical name of a complete bounded
 * CompositeState, command tag, then arguments 0..3. Lean reconstructs the
 * complete state by authoritative replay; callers cannot supply individual
 * state projections or post-state fragments. The result canonically names
 * the exact typed authoritativeGate result and next state.
 *
 * All fields are logical uint64_t values. There are no caller-owned buffers,
 * so state/result aliasing, alignment, pointer identity, and partial writes are
 * inapplicable. Calls are pure, reentrant, and have no generated state cell.
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
