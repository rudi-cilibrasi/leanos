/* Hosted post-state replay (#476): generated C of LeanOS.PostStateProjection
   against the Lean-evaluated corpus in poststate.h.  Each vector projects a
   frame's bytes or one capability row after a canonical model state, so a
   generated scrub or capability-table update that diverges from Lean shows
   up as a projection mismatch rather than hiding behind a reply word. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#define LEANOS_BOUNDARY_ABI_OBJECTS 1
#include "boundary-abi.h"
#include "poststate.h"

extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_PostStateProjection(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);
#define REGISTER_BOUNDARY(symbol) \
    leanos_register_boundary_target(#symbol, (void *)(uintptr_t)&symbol)

static uint64_t dispatch(const struct poststate_vector *v) {
    switch (v->adapter) {
    case 0: return leanos_frame_scrub_projection(v->words[0], v->words[1]);
    case 1:
        return leanos_frame_budget_capability_row(
            v->words[0], v->words[1], v->words[2]);
    case 2:
        return leanos_mixed_capability_row(v->words[0], v->words[1], v->words[2]);
    default:
        return UINT64_MAX;
    }
}

/* The switch above must name exactly the adapters Lean generated. */
static int adapter_matches(unsigned id, uintptr_t symbol, unsigned arity) {
    switch (id) {
    case 0: return symbol == (uintptr_t)&leanos_frame_scrub_projection && arity == 2;
    case 1: return symbol == (uintptr_t)&leanos_frame_budget_capability_row && arity == 3;
    case 2: return symbol == (uintptr_t)&leanos_mixed_capability_row && arity == 3;
    default: return 0;
    }
}

#define POSTSTATE_CHECK_ADAPTER(id, symbol, arity) \
    if (!adapter_matches(id, (uintptr_t)&symbol, arity)) { \
        fprintf(stderr, "poststate adapter table mismatch: %d %s\n", id, #symbol); \
        adapters_ok = 0; \
    }

static lean_object *run_host(int argc, char **argv) {
    (void)argc;
    (void)argv;
    REGISTER_BOUNDARY(leanos_frame_scrub_projection);
    REGISTER_BOUNDARY(leanos_frame_budget_capability_row);
    REGISTER_BOUNDARY(leanos_mixed_capability_row);
    int adapters_ok = 1;
    LEANOS_POSTSTATE_ADAPTERS(POSTSTATE_CHECK_ADAPTER)
    if (!adapters_ok) {
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("post-state adapter table mismatch")));
    }
    for (unsigned i = 0; i < POSTSTATE_VECTOR_COUNT; ++i) {
        struct poststate_vector vector = poststate_vectors[i];
#ifdef LEANOS_FIXTURE_POSTSTATE_UNSCRUBBED_REALLOCATION
        /* Publish frame 100 to B with the bytes A left behind: the state a
           reallocation that skipped the scrub would expose. */
        if (i == POSTSTATE_INDEX_FRAME_SCRUB_B_FRESH_FRAME_100_REPUBLISHED_ZERO) {
            vector.words[0] = poststate_vectors[
                POSTSTATE_INDEX_FRAME_SCRUB_A_TERMINATED_FRAME_100_RELEASED_DIRTY].words[0];
        }
#endif
        uint64_t got = dispatch(&vector);
#ifdef LEANOS_FIXTURE_POSTSTATE_STALE_GENERATION
        /* Keep the revoked capability's identity in the fresh copy's row:
           the stale generation a handle check would wrongly accept. */
        if (i == POSTSTATE_INDEX_MIXED_ROW_CAPABILITY_COPIED_SUBJECT_2_SLOT_3) {
            got = (got & ~(UINT64_C(0xffff) << 40)) |
                (poststate_vectors[
                    POSTSTATE_INDEX_MIXED_ROW_TRANSFER_ACCEPTED_SUBJECT_2_SLOT_3].expected &
                    (UINT64_C(0xffff) << 40));
        }
#endif
        if (got != vector.expected) {
            fprintf(stderr,
                "poststate mismatch: vector=%u operation=%s field=projection expected=%llu got=%llu\n",
                i, vector.id, vector.expected, (unsigned long long)got);
            return lean_io_result_mk_error(lean_mk_io_user_error(
                lean_mk_string("post-state projection mismatch")));
        }
        printf("POSTSTATE/%u id=%s result=%llu\n", i, vector.id,
            (unsigned long long)got);
    }
    puts("Hosted generated-C post-state projection replay passed");
    return lean_io_result_mk_ok(lean_box(0));
}

int main(int argc, char **argv) {
    argv = lean_setup_args(argc, argv);
    lean_initialize();
    lean_object *result = initialize_leanos_LeanOS_PostStateProjection(1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(result)) {
        lean_dec(result);
        lean_init_task_manager();
        result = lean_run_main(&run_host, argc, argv);
    }
    lean_finalize_task_manager();
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        lean_dec(result);
        return 1;
    }
    lean_dec(result);
    return 0;
}
