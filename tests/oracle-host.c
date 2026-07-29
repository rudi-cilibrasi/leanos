#include <stdint.h>
#include <stdio.h>
#include "corpus.h"
#include "leanos/composite-dispatcher.h"
#include "../boot/generated-boundary-abi.h"

extern uint64_t leanos_boot_transition(uint64_t, uint64_t);
extern uint64_t leanos_syscall_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_ipc_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_preemption_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_resumable_preemption_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                                  uint64_t);
extern uint64_t leanos_boot_select_frame(uint64_t, uint64_t, uint64_t, uint64_t,
                                         uint64_t, uint64_t);
extern uint64_t leanos_user_return_demo(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_blocking_ipc_demo(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_capability_reuse_demo(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_entry_demo(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_extended_state_denial_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                                   uint64_t, uint64_t);
extern uint64_t leanos_privilege_entry_control_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                                     uint64_t, uint64_t);
extern uint64_t leanos_fault_dispatch_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                            uint64_t, uint64_t);
extern uint64_t leanos_direct_port_io_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                            uint64_t, uint64_t);
extern uint64_t leanos_nmi_demo(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_phase_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                        uint64_t);
extern uint64_t leanos_stale_translation_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                               uint64_t, uint64_t);
extern uint64_t leanos_page_fault_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                        uint64_t);
extern uint64_t leanos_page_fault_dispatch_regression_demo(uint64_t);
extern uint64_t leanos_page_fault_diagnostic_regression_demo(uint64_t);
extern void leanos_register_boundary_target(const char *, void *);
#define REGISTER_BOUNDARY(symbol) \
    leanos_register_boundary_target(#symbol, (void *)(uintptr_t)&symbol)
uint8_t lean_uint64_dec_eq(uint64_t left, uint64_t right) { return left == right; }

int main(void) {
    REGISTER_BOUNDARY(leanos_boot_transition);
    REGISTER_BOUNDARY(leanos_syscall_demo);
    REGISTER_BOUNDARY(leanos_ipc_demo);
    REGISTER_BOUNDARY(leanos_preemption_demo);
    REGISTER_BOUNDARY(leanos_resumable_preemption_demo);
    REGISTER_BOUNDARY(leanos_boot_select_frame);
    REGISTER_BOUNDARY(leanos_user_return_demo);
    REGISTER_BOUNDARY(leanos_authorize_page_fault_snapshot);
    REGISTER_BOUNDARY(leanos_page_fault_demo);
    REGISTER_BOUNDARY(leanos_nmi_demo);
    REGISTER_BOUNDARY(leanos_entry_demo);
    REGISTER_BOUNDARY(leanos_boot_phase_demo);
    REGISTER_BOUNDARY(leanos_blocking_ipc_demo);
    REGISTER_BOUNDARY(leanos_capability_reuse_demo);
    REGISTER_BOUNDARY(leanos_extended_state_denial_demo);
    REGISTER_BOUNDARY(leanos_privilege_entry_control_demo);
    REGISTER_BOUNDARY(leanos_fault_dispatch_demo);
    REGISTER_BOUNDARY(leanos_page_fault_dispatch_transition);
    REGISTER_BOUNDARY(leanos_page_fault_dispatch_regression_demo);
    REGISTER_BOUNDARY(leanos_page_fault_diagnostic_regression_demo);
    REGISTER_BOUNDARY(leanos_direct_port_io_demo);
    REGISTER_BOUNDARY(leanos_stale_translation_demo);
    REGISTER_BOUNDARY(leanos_frame_budget_mapping_page);
    REGISTER_BOUNDARY(leanos_composite_dispatch);
    REGISTER_BOUNDARY(leanos_validate_q35_dma_snapshot);

    /* Exercise the production ABI wrappers themselves so --gc-sections cannot
       discard them from the ordinary or sanitizer replay. Invalid all-zero
       snapshots must be rejected, but still traverse each generated wrapper. */
    if (leanos_authorize_page_fault_snapshot(
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) != 0) {
        fputs("invalid canonical page-fault snapshot was accepted\n", stderr);
        return 1;
    }
    (void)leanos_page_fault_dispatch_transition(
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    if (leanos_frame_budget_mapping_page(
            LEANOS_COMPOSITE_STATE_BUDGET_INITIAL,
            LEANOS_COMPOSITE_COMMAND_BUDGET_ALLOCATE_A) != 4095 ||
        leanos_frame_budget_mapping_page(
            LEANOS_COMPOSITE_STATE_BUDGET_A_TERMINATED,
            LEANOS_COMPOSITE_COMMAND_BUDGET_PUBLISH_FRESH_B) != 4095 ||
        leanos_frame_budget_mapping_page(
            LEANOS_COMPOSITE_STATE_BUDGET_INITIAL,
            LEANOS_COMPOSITE_COMMAND_BUDGET_PUBLISH_FRESH_B) != UINT64_MAX) {
        fputs("generated frame-budget mapping policy drifted\n", stderr);
        return 1;
    }
    if (leanos_validate_q35_dma_snapshot(
            1, UINT64_C(0x000800020002),
            UINT64_C(0x0006000029c08086), UINT64_C(0x0001),
            UINT64_C(0x0003000011111234), UINT64_C(0x0001),
            0, 0,
            UINT64_C(0x0006010029188086), UINT64_C(0xc001),
            UINT64_C(0x0001060129228086), UINT64_C(0x8001),
            UINT64_C(0x000c050029308086), UINT64_C(0x8001)) != 0) {
        fputs("canonical q35 DMA snapshot was rejected\n", stderr);
        return 1;
    }
    if (leanos_validate_q35_dma_snapshot(
            1, UINT64_C(0x000800020002),
            UINT64_C(0x0006000029c08086), UINT64_C(0x0001),
            UINT64_C(0x0003000011111234), UINT64_C(0x0011),
            0, 0,
            UINT64_C(0x0006010029188086), UINT64_C(0xc001),
            UINT64_C(0x0001060129228086), UINT64_C(0x8001),
            UINT64_C(0x000c050029308086), UINT64_C(0x8001)) != 8) {
        fputs("bus-master-enabled q35 DMA snapshot was not rejected\n", stderr);
        return 1;
    }

    for (unsigned i = 0; i < ORACLE_VECTOR_COUNT; ++i) {
        const struct oracle_vector *v = &oracle_vectors[i];
        unsigned argc = v->argc;
#ifdef LEANOS_FIXTURE_COMPOSITE_TRUNCATED
        if (v->adapter == 18) {
            argc = 5;
        }
#endif
        if (v->adapter == 18 && argc != LEANOS_COMPOSITE_INPUT_WORDS) {
            fprintf(stderr, "oracle malformed arity: %u %s expected=%u got=%u\n",
                i, v->id, LEANOS_COMPOSITE_INPUT_WORDS, argc);
            return 1;
        }
        uint64_t composite_state = v->words[0];
        uint64_t composite_tag = v->words[1];
        uint64_t composite_arg0 = v->words[2];
        uint64_t composite_arg1 = v->words[3];
        uint64_t composite_arg2 = v->words[4];
        uint64_t composite_arg3 = v->words[5];
        (void)composite_state;
        (void)composite_tag;
        (void)composite_arg0;
        (void)composite_arg1;
        (void)composite_arg2;
        (void)composite_arg3;
#ifdef LEANOS_FIXTURE_COMPOSITE_WRONG_VERSION
        if (i == ORACLE_INDEX_COMPOSITE_CREATE_SUBJECT) {
            composite_state = UINT64_C(2);
        }
#endif
#ifdef LEANOS_FIXTURE_COMPOSITE_RESERVED_BITS
        if (i == ORACLE_INDEX_COMPOSITE_CREATE_SUBJECT) {
            composite_tag = UINT64_C(0x10001);
        }
#endif
#ifdef LEANOS_FIXTURE_COMPOSITE_STALE_REPLAY
        if (i == ORACLE_INDEX_COMPOSITE_REJECT_UNKNOWN_SYSCALL) {
            composite_state = UINT64_C(1);
        }
#endif
#ifdef LEANOS_FIXTURE_COMPOSITE_FORGED_CONTEXT
        if (i == ORACLE_INDEX_COMPOSITE_CREATE_SUBJECT) {
            composite_arg3 = UINT64_C(1);
        }
#endif
#ifdef LEANOS_FIXTURE_COMPOSITE_HANDLE_CORRUPTION
        if (i == ORACLE_INDEX_COMPOSITE_REJECT_STALE_MAP_HANDLE) {
            composite_arg0 = UINT64_C(0xffff);
        }
#endif
#ifdef LEANOS_FIXTURE_FRAME_BUDGET_GLOBAL_COUNTER
        if (i == ORACLE_INDEX_FRAME_BUDGET_B_PEER_ALLOCATE) {
            composite_state = UINT64_C(0x4101);
        }
#endif
#ifdef LEANOS_FIXTURE_FRAME_BUDGET_CROSS_CHARGE
        if (i == ORACLE_INDEX_FRAME_BUDGET_B_PEER_ALLOCATE) {
            composite_arg2 = UINT64_C(1);
        }
#endif
#ifdef LEANOS_FIXTURE_FRAME_BUDGET_USER_OWNER
        if (i == ORACLE_INDEX_FRAME_BUDGET_A_ALLOCATE) {
            composite_arg2 = UINT64_C(2);
        }
#endif
        uint64_t got = v->adapter == 0
            ? leanos_boot_transition(v->words[0], v->words[1])
            : v->adapter == 1
                ? leanos_syscall_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                : v->adapter == 2
                    ? leanos_ipc_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                : v->adapter == 3
                    ? leanos_preemption_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                : v->adapter == 4
                    ? leanos_resumable_preemption_demo(v->words[0], v->words[1], v->words[2],
                        v->words[3], v->words[4])
                    : v->adapter == 5
                        ? leanos_boot_select_frame(v->words[0], v->words[1], v->words[2],
                            v->words[3], v->words[4], v->words[5])
                        : v->adapter == 6
                            ? leanos_user_return_demo(v->words[0], v->words[1], v->words[2],
                                v->words[3], v->words[4])
                            : v->adapter == 7
                                ? leanos_blocking_ipc_demo(v->words[0], v->words[1], v->words[2],
                                    v->words[3], v->words[4])
                                : v->adapter == 8
                                    ? leanos_capability_reuse_demo(v->words[0], v->words[1],
                                        v->words[2], v->words[3], v->words[4])
                                    : v->adapter == 9
                                        ? leanos_entry_demo(v->words[0], v->words[1], v->words[2],
                                            v->words[3], v->words[4])
                                        : v->adapter == 10
                                            ? leanos_extended_state_denial_demo(v->words[0],
                                                v->words[1], v->words[2], v->words[3],
                                                v->words[4], v->words[5])
                                            : v->adapter == 11
                                                ? leanos_privilege_entry_control_demo(v->words[0],
                                                v->words[1], v->words[2], v->words[3],
                                                v->words[4], v->words[5])
                                                : v->adapter == 12
                                                    ? leanos_fault_dispatch_demo(v->words[0],
                                                    v->words[1], v->words[2], v->words[3],
                                                    v->words[4], v->words[5])
                                                    : v->adapter == 13
                                                        ? leanos_direct_port_io_demo(v->words[0],
                                                        v->words[1], v->words[2], v->words[3],
                                                        v->words[4], v->words[5])
                                                        : v->adapter == 14
                                                            ? leanos_nmi_demo(v->words[0],
                                                            v->words[1], v->words[2],
                                                            v->words[3], v->words[4])
                                                            : v->adapter == 15
                                                            ? leanos_boot_phase_demo(v->words[0],
                                                            v->words[1], v->words[2],
                                                            v->words[3], v->words[4])
                                                            : v->adapter == 16
                                                            ? leanos_stale_translation_demo(
                                                            v->words[0], v->words[1], v->words[2],
                                                            v->words[3], v->words[4], v->words[5])
                                                            : v->adapter == 17
                                                            ? leanos_page_fault_demo(v->words[0],
                                                            v->words[1], v->words[2],
                                                            v->words[3], v->words[4])
                                                            : v->adapter == 18
#ifdef LEANOS_FIXTURE_COMPOSITE_OLD_STATELESS
                                                            ? leanos_syscall_demo(v->words[0],
                                                            v->words[1], v->words[2], v->words[3])
#else
                                                            ? leanos_composite_dispatch(
                                                            composite_state, composite_tag,
                                                            composite_arg0, composite_arg1,
                                                            composite_arg2, composite_arg3)
#endif
                                                            : UINT64_MAX;
#ifdef LEANOS_FIXTURE_COMPOSITE_OUTPUT_CORRUPTION
        if (v->adapter == 18) {
            got ^= UINT64_C(1);
        }
#endif
#ifdef LEANOS_FIXTURE_FRAME_BUDGET_RELABEL_SUCCESS
        if (i == ORACLE_INDEX_FRAME_BUDGET_A_AT_LIMIT) {
            got = UINT64_C(0x404101);
        }
#endif
#ifdef LEANOS_FIXTURE_FRAME_BUDGET_PARTIAL_PUBLICATION
        if (i == ORACLE_INDEX_FRAME_BUDGET_A_AT_LIMIT) {
            got ^= UINT64_C(0x100);
        }
#endif
#ifdef LEANOS_FIXTURE_FRAME_BUDGET_DOUBLE_CREDIT
        if (i == ORACLE_INDEX_FRAME_BUDGET_TERMINATE_A) {
            got ^= UINT64_C(0x100);
        }
#endif
        if (got != v->expected) {
            fprintf(stderr,
                "oracle mismatch: vector=%u operation=%s field=reply expected=%llu got=%llu\n",
                i, v->id,
                v->expected, (unsigned long long)got);
            return 1;
        }
        printf("ORACLE/%u id=%s result=%llu\n", i, v->id, (unsigned long long)got);
    }
    if (leanos_page_fault_dispatch_regression_demo(0) != UINT64_C(2) ||
        leanos_page_fault_dispatch_regression_demo(1) != UINT64_C(2)) {
        fputs("page-fault rich/scalar regression route was not fatal\n", stderr);
        return 1;
    }
    if (leanos_page_fault_diagnostic_regression_demo(0) != UINT64_C(2) ||
        leanos_page_fault_diagnostic_regression_demo(1) != UINT64_C(2)) {
        fputs("page-fault stale/forged diagnostic route was not fatal\n", stderr);
        return 1;
    }
    return 0;
}
