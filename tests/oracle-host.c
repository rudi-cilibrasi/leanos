#include <stdint.h>
#include <stdio.h>
#include "corpus.h"
#include "leanos/composite-dispatcher.h"

#include "leanos/oracle-dispatch.h"
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
    REGISTER_BOUNDARY(leanos_boot_consume_exact_projection);
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
    REGISTER_BOUNDARY(leanos_iotlb_publication_demo);
    REGISTER_BOUNDARY(leanos_assigned_edu_reuse_publication);
    REGISTER_BOUNDARY(leanos_assigned_edu_reuse_protocol);
    REGISTER_BOUNDARY(leanos_assigned_edu_reuse_release_gate);
    REGISTER_BOUNDARY(leanos_assigned_edu_reuse_fresh_publication);
    REGISTER_BOUNDARY(leanos_frame_budget_mapping_page);
    REGISTER_BOUNDARY(leanos_frame_budget_invalidation_effect);
    REGISTER_BOUNDARY(leanos_composite_dispatch);
    REGISTER_BOUNDARY(leanos_composite_dispatch_value);
    REGISTER_BOUNDARY(leanos_validate_q35_dma_snapshot);
    REGISTER_BOUNDARY(leanos_validate_vtd_activation);
    REGISTER_BOUNDARY(leanos_validate_assigned_edu_projection);
    REGISTER_BOUNDARY(leanos_validate_assigned_edu_transfer);
    REGISTER_BOUNDARY(leanos_validate_assigned_edu_fault);

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
    if (leanos_frame_budget_invalidation_effect(
            LEANOS_COMPOSITE_STATE_BUDGET_B_ALLOCATED,
            LEANOS_COMPOSITE_COMMAND_BUDGET_TERMINATE_A) !=
            LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN ||
        leanos_frame_budget_invalidation_effect(
            LEANOS_COMPOSITE_STATE_BUDGET_A_ALLOCATED,
            LEANOS_COMPOSITE_COMMAND_BUDGET_RELEASE_A) !=
            LEANOS_FRAME_BUDGET_RELEASE_FLUSH_TOKEN ||
        leanos_frame_budget_invalidation_effect(
            LEANOS_COMPOSITE_STATE_BUDGET_B_ALLOCATED,
            LEANOS_COMPOSITE_COMMAND_BUDGET_RELEASE_A) != 0 ||
        leanos_frame_budget_invalidation_effect(
            LEANOS_COMPOSITE_STATE_BUDGET_A_ALLOCATED,
            LEANOS_COMPOSITE_COMMAND_BUDGET_TERMINATE_A) != 0) {
        fputs("generated frame-budget invalidation policy drifted\n", stderr);
        return 1;
    }
    if (leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0) != 0 ||
        leanos_assigned_edu_reuse_publication(
            2, 1, 16, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0) != 0 ||
        leanos_assigned_edu_reuse_publication(
            1, 2, 16, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 17, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 1, 0, 1, UINT64_C(0x1000), 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 1, 0, 1, 0, 0, 2, 0) != 1 ||
        leanos_assigned_edu_reuse_publication(
            1, 1, 16, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1,
            UINT64_C(0x1000)) != 1 ||
        leanos_assigned_edu_reuse_publication(
            3, 1, 16, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0) != 4) {
        fputs("generated assigned-EDU reuse publication policy drifted\n", stderr);
        return 1;
    }
    if (leanos_assigned_edu_reuse_protocol(1, 1, 1, 0) != 0 ||
        leanos_assigned_edu_reuse_protocol(0, 1, 1, 0) != 2 ||
        leanos_assigned_edu_reuse_protocol(1, 0, 1, 0) != 1 ||
        leanos_assigned_edu_reuse_protocol(1, 1, 2, 0) != 3 ||
        leanos_assigned_edu_reuse_protocol(1, 1, 1, 1) != 4) {
        fputs("generated assigned-EDU reuse protocol drifted\n", stderr);
        return 1;
    }
    if (leanos_assigned_edu_reuse_release_gate(0, 0, 0) != 1 ||
        leanos_assigned_edu_reuse_release_gate(1, 1, 0) != 2 ||
        leanos_assigned_edu_reuse_release_gate(1, 0, 1) != 3 ||
        leanos_assigned_edu_reuse_release_gate(1, 0, 0) != 0) {
        fputs("assigned EDU release gate accepted stale authority\n", stderr);
        return 1;
    }
    if (leanos_assigned_edu_reuse_fresh_publication(0, 0) != 0 ||
        leanos_assigned_edu_reuse_fresh_publication(1, 0) != 1 ||
        leanos_assigned_edu_reuse_fresh_publication(2, 0) != 1 ||
        leanos_assigned_edu_reuse_fresh_publication(3, 0) != 1 ||
        leanos_assigned_edu_reuse_fresh_publication(0, 1) != 2 ||
        leanos_assigned_edu_reuse_fresh_publication(0, 2) != 2 ||
        leanos_assigned_edu_reuse_fresh_publication(0, 3) != 3) {
        fputs("assigned EDU fresh publication ordering drifted\n", stderr);
        return 1;
    }
    if (leanos_validate_q35_dma_snapshot(
            1, UINT64_C(0x0001000800020002),
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
            1, UINT64_C(0x0001000800020002),
            UINT64_C(0x0006000029c08086), UINT64_C(0x0001),
            UINT64_C(0x0003000011111234), UINT64_C(0x0011),
            0, 0,
            UINT64_C(0x0006010029188086), UINT64_C(0xc001),
            UINT64_C(0x0001060129228086), UINT64_C(0x8001),
            UINT64_C(0x000c050029308086), UINT64_C(0x8001)) != 8) {
        fputs("bus-master-enabled q35 DMA snapshot was not rejected\n", stderr);
        return 1;
    }
    if (leanos_validate_vtd_activation(
            1, UINT64_C(0x0001000800020002),
            UINT64_C(0x10), UINT64_C(0x00d2008c22260206), UINT64_C(0x0f02),
            UINT64_C(0xc0000000), 0,
            UINT64_C(0x174000), UINT64_C(0x174000),
            UINT64_C(0x87654321)) != 0) {
        fputs("canonical VT-d activation was rejected\n", stderr);
        return 1;
    }
    if (leanos_validate_vtd_activation(
            1, UINT64_C(0x0001000800020002),
            UINT64_C(0x10), UINT64_C(0x00d2008c22260206), UINT64_C(0x0f02),
            UINT64_C(0xc0000000), 0,
            UINT64_C(0x174000), UINT64_C(0x174000),
            UINT64_C(0x87653421)) != 9) {
        fputs("reordered VT-d activation journal was not rejected\n", stderr);
        return 1;
    }
    if (leanos_validate_assigned_edu_projection(
            1, UINT64_C(0x0001000800020003),
            0, 0, 1, 0, 1, 0, 16,
            3, 4, 5, 7, 8,
            0, 16, 0, 1, 0, 1,
            16, 16, 0, 1, 16, 2) != 0) {
        fputs("canonical assigned-EDU projection was rejected\n", stderr);
        return 1;
    }
    if (leanos_validate_assigned_edu_projection(
            1, UINT64_C(0x0001000800020003),
            0, 0, 1, 0, 1, 0, 16,
            3, 4, 5, 7, 8,
            0, 16, 0, 1, 0, 3,
            16, 16, 0, 1, 16, 2) != 5) {
        fputs("widened assigned-EDU read permission was not rejected\n", stderr);
        return 1;
    }
    if (leanos_validate_assigned_edu_transfer(1, 0, 1, 0, 16, 1) != 0 ||
        leanos_validate_assigned_edu_transfer(1, 0, 1, 16, 16, 2) != 0) {
        fputs("canonical assigned-EDU transfers were rejected\n", stderr);
        return 1;
    }
    if (leanos_validate_assigned_edu_transfer(1, 0, 1, 0, 16, 2) != 5 ||
        leanos_validate_assigned_edu_transfer(1, 0, 1, 16, 16, 1) != 5) {
        fputs("wrong-direction assigned-EDU transfer was not denied\n", stderr);
        return 1;
    }
    if (leanos_validate_assigned_edu_transfer(1, 0, 1, 8, 16, 1) != 4 ||
        leanos_validate_assigned_edu_transfer(1, 1, 1, 0, 16, 1) != 3) {
        fputs("out-of-window or wrong-source assigned-EDU transfer was not denied\n",
            stderr);
        return 1;
    }
    if (leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 4096, 1, 2, 4096,
            UINT64_C(0xc0ffff0600000010)) != 0 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 0, 2, 2, 0,
            UINT64_C(0x80ffff0500000010)) != 0 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 8192, 1, 2, 8192,
            UINT64_C(0xc0ffff0600000010)) != 0 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 4096, 1, 2, 4096,
            UINT64_C(0xc000000500000010)) != 6) {
        fputs("assigned-EDU hardware fault binding was not enforced\n", stderr);
        return 1;
    }
    if (leanos_validate_assigned_edu_fault(
            0, 0, 0, 1, 4096, 1, 2, 4096,
            UINT64_C(0xc0ffff0600000010)) != 1 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 4096, 3, 2, 4096,
            UINT64_C(0xc0ffff0600000010)) != 2 ||
        leanos_validate_assigned_edu_fault(
            1, 1, 0, 1, 4096, 1, 2, 4096,
            UINT64_C(0xc0ffff0600000010)) != 3 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 1, 1, 4096, 1, 2, 4096,
            UINT64_C(0xc0ffff0600000010)) != 3 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 2, 4096, 1, 2, 4096,
            UINT64_C(0xc0ffff0600000010)) != 3 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 0, 1, 2, 4096,
            UINT64_C(0xc0ffff0600000010)) != 4 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 4096, 1, 0, 4096,
            UINT64_C(0xc0ffff0600000010)) != 4 ||
        leanos_validate_assigned_edu_fault(
            1, 0, 0, 1, 4096, 1, 2, 0,
            UINT64_C(0xc0ffff0600000010)) != 5) {
        fputs("forged assigned-EDU fault fields were not rejected\n", stderr);
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
        struct oracle_vector dispatch_vector = *v;
        dispatch_vector.words[0] = composite_state;
        dispatch_vector.words[1] = composite_tag;
        dispatch_vector.words[2] = composite_arg0;
        dispatch_vector.words[3] = composite_arg1;
        dispatch_vector.words[4] = composite_arg2;
        dispatch_vector.words[5] = composite_arg3;
        uint64_t got;
        uint64_t got_value = 0;
#ifdef LEANOS_FIXTURE_COMPOSITE_OLD_STATELESS
        if (v->adapter == 18) {
            got = leanos_syscall_demo(
                v->words[0], v->words[1], v->words[2], v->words[3]);
        } else {
            got = leanos_oracle_dispatch(&dispatch_vector);
        }
#else
        got = leanos_oracle_dispatch(&dispatch_vector);
#endif
        if (v->adapter == 18) {
            got_value = leanos_composite_dispatch_value(
                composite_state, composite_tag, composite_arg0,
                composite_arg1, composite_arg2, composite_arg3);
        }
#ifdef LEANOS_FIXTURE_COMPOSITE_OUTPUT_CORRUPTION
        if (v->adapter == 18) {
            got ^= UINT64_C(1);
        }
#endif
#ifdef LEANOS_FIXTURE_COMPOSITE_VALUE_CORRUPTION
        if (i == ORACLE_INDEX_COMPOSITE_MIXED_TRANSFER_ACCEPT) {
            got_value ^= UINT64_C(1);
        }
#endif
#ifdef LEANOS_FIXTURE_COMPOSITE_VALUE_OMISSION
        if (i == ORACLE_INDEX_COMPOSITE_MIXED_TRANSFER_ACCEPT) {
            got_value = 0;
        }
#endif
#ifdef LEANOS_FIXTURE_COMPOSITE_VALUE_LEAK
        if (i == ORACLE_INDEX_COMPOSITE_MIXED_TRANSFER_OFFER) {
            got_value = UINT64_C(0x60003);
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
        if (got_value != v->expected_value) {
            fprintf(stderr,
                "oracle mismatch: vector=%u operation=%s field=value expected=%llu got=%llu\n",
                i, v->id, v->expected_value, (unsigned long long)got_value);
            return 1;
        }
        printf("ORACLE/%u id=%s result=%llu value=%llu\n", i, v->id,
            (unsigned long long)got, (unsigned long long)got_value);
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
