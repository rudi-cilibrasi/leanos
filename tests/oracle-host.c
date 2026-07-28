#include <stdint.h>
#include <stdio.h>
#include "corpus.h"
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

    for (unsigned i = 0; i < ORACLE_VECTOR_COUNT; ++i) {
        const struct oracle_vector *v = &oracle_vectors[i];
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
                                                            : leanos_page_fault_demo(v->words[0],
                                                            v->words[1], v->words[2],
                                                            v->words[3], v->words[4]);
        if (got != v->expected) {
            fprintf(stderr, "oracle mismatch: %u %s expected=%llu got=%llu\n", i, v->id,
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
