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
 * Exactly six input words are required by the surrounding corpus format;
 * truncation is rejected by that caller before this scalar function is called.
 *
 * Every state and command word has ABI version 1 in bits 0..7. State bits
 * 8..15 select one of eight canonical states and all upper bits are reserved.
 * Command tags use bits 8..15 to select one of twelve commands and all upper
 * bits are reserved. Arguments not named by a command must be zero. A success
 * result uses bits 0..7 for the version, 8..15 for the next-state selector,
 * 16..23 for the typed-reply selector, and reserves bits 24..63. Error words
 * are the closed values listed below and never authorize an operation.
 */
#define LEANOS_COMPOSITE_ABI_VERSION UINT64_C(1)
#define LEANOS_COMPOSITE_INPUT_WORDS 6U
#define LEANOS_COMPOSITE_RESULT_WORDS 1U
#define LEANOS_COMPOSITE_STATE_COUNT 8U
#define LEANOS_COMPOSITE_COMMAND_COUNT 12U

#define LEANOS_COMPOSITE_STATE_INITIAL UINT64_C(0x0001)
#define LEANOS_COMPOSITE_STATE_SUBJECT_CREATED UINT64_C(0x0101)
#define LEANOS_COMPOSITE_STATE_UNKNOWN_SYSCALL_REJECTED UINT64_C(0x0201)
#define LEANOS_COMPOSITE_STATE_MALFORMED_MAP_REJECTED UINT64_C(0x0301)
#define LEANOS_COMPOSITE_STATE_SCHEDULER_OBSERVED UINT64_C(0x0401)
#define LEANOS_COMPOSITE_STATE_SUBJECT_TERMINATED UINT64_C(0x0501)
#define LEANOS_COMPOSITE_STATE_FATAL_ENTERED UINT64_C(0x0601)
#define LEANOS_COMPOSITE_STATE_POST_FATAL_REJECTED UINT64_C(0x0701)

#define LEANOS_COMPOSITE_COMMAND_CREATE_SUBJECT_ONE UINT64_C(0x0101)
#define LEANOS_COMPOSITE_COMMAND_REJECT_UNKNOWN_SYSCALL UINT64_C(0x0201)
#define LEANOS_COMPOSITE_COMMAND_REJECT_MALFORMED_MAP UINT64_C(0x0301)
#define LEANOS_COMPOSITE_COMMAND_OBSERVE_SCHEDULER UINT64_C(0x0401)
#define LEANOS_COMPOSITE_COMMAND_TERMINATE_SUBJECT_ONE UINT64_C(0x0501)
#define LEANOS_COMPOSITE_COMMAND_ENTER_FATAL_KERNEL_FAULT UINT64_C(0x0601)
#define LEANOS_COMPOSITE_COMMAND_ATTEMPT_POST_FATAL_SCHEDULE UINT64_C(0x0701)
#define LEANOS_COMPOSITE_COMMAND_REJECT_STALE_MAP_HANDLE UINT64_C(0x0801)
#define LEANOS_COMPOSITE_COMMAND_REJECT_NONBLOCKING_RECEIVE UINT64_C(0x0901)
#define LEANOS_COMPOSITE_COMMAND_REJECT_CAPABILITY_COPY UINT64_C(0x0a01)
#define LEANOS_COMPOSITE_COMMAND_REJECT_BLOCKING_CANCEL UINT64_C(0x0b01)
#define LEANOS_COMPOSITE_COMMAND_REJECT_DEFERRED_DRAIN UINT64_C(0x0c01)

#define LEANOS_COMPOSITE_ERROR_WRONG_VERSION UINT64_C(0xff01)
#define LEANOS_COMPOSITE_ERROR_RESERVED_BITS UINT64_C(0xff02)
#define LEANOS_COMPOSITE_ERROR_UNKNOWN_STATE UINT64_C(0xff03)
#define LEANOS_COMPOSITE_ERROR_UNKNOWN_COMMAND UINT64_C(0xff04)
#define LEANOS_COMPOSITE_ERROR_NONCANONICAL_ARGUMENTS UINT64_C(0xff05)
#define LEANOS_COMPOSITE_ERROR_INVALID_SEQUENCE UINT64_C(0xff06)

uint64_t leanos_composite_dispatch(
    uint64_t state,
    uint64_t command,
    uint64_t arg0,
    uint64_t arg1,
    uint64_t arg2,
    uint64_t arg3);

#endif
