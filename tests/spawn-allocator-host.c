/* Hosted spawn-allocator replay (#575): the Lake-generated C of
   LeanOS.SpawnAllocatorWords (its SpawnAllocatorBoot exports) against the
   corpus that `lake exe
   leanos-spawn-allocator` evaluates from the specification (decode, run the
   allocator, encode) over many allocator records.  Every vector checks the
   reply, the value word and all thirteen successor words, so a generated
   successor word that diverges from the allocator shows up even when the
   reply agrees. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#define LEANOS_BOUNDARY_ABI_OBJECTS 1
#include "boundary-abi.h"
#include "spawn-allocator.h"

extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_SpawnAllocatorWords(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);
#define REGISTER_BOUNDARY(symbol) \
    leanos_register_boundary_target(#symbol, (void *)(uintptr_t)&symbol)

#define STATE(v) \
    (v)->state[0], (v)->state[1], (v)->state[2], (v)->state[3], (v)->state[4], \
    (v)->state[5], (v)->state[6], (v)->state[7], (v)->state[8], (v)->state[9], \
    (v)->state[10], (v)->state[11], (v)->state[12]
#define INPUT(v) (v)->input[0], (v)->input[1], (v)->input[2], (v)->input[3], (v)->input[4]

static uint64_t reply_of(const struct spawn_allocator_vector *v) {
    if (v->kind == 's') return leanos_spawn_allocator_syscall(STATE(v), INPUT(v));
    return leanos_spawn_allocator_kernel(STATE(v), INPUT(v));
}

static uint64_t value_of(const struct spawn_allocator_vector *v) {
    if (v->kind == 's') return leanos_spawn_allocator_syscall_value(STATE(v), INPUT(v));
    return leanos_spawn_allocator_kernel_value(STATE(v), INPUT(v));
}

static uint64_t next_of(const struct spawn_allocator_vector *v, uint64_t index) {
    if (v->kind == 's') return leanos_spawn_allocator_syscall_next(index, STATE(v), INPUT(v));
    return leanos_spawn_allocator_kernel_next(index, STATE(v), INPUT(v));
}

static lean_object *fail_vector(unsigned index, const char *field, unsigned long long expected,
                                unsigned long long got) {
    fprintf(stderr, "spawn-allocator mismatch: vector=%u field=%s expected=%llu got=%llu\n",
        index, field, expected, got);
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("spawn-allocator mismatch")));
}

static lean_object *run_host(int argc, char **argv) {
    (void)argc;
    (void)argv;
    REGISTER_BOUNDARY(leanos_spawn_allocator_seed);
    REGISTER_BOUNDARY(leanos_spawn_allocator_syscall);
    REGISTER_BOUNDARY(leanos_spawn_allocator_syscall_value);
    REGISTER_BOUNDARY(leanos_spawn_allocator_syscall_next);
    REGISTER_BOUNDARY(leanos_spawn_allocator_kernel);
    REGISTER_BOUNDARY(leanos_spawn_allocator_kernel_value);
    REGISTER_BOUNDARY(leanos_spawn_allocator_kernel_next);
    for (uint64_t index = 0; index < 13; ++index) {
        uint64_t got = leanos_spawn_allocator_seed(index);
        if (got != spawn_allocator_seed_words[index])
            return fail_vector((unsigned)index, "seed", spawn_allocator_seed_words[index], got);
    }
    unsigned long long accepted = 0, rejected = 0, refused = 0, errors = 0;
    int fixture_applied = 0;
    for (unsigned i = 0; i < SPAWN_ALLOCATOR_VECTOR_COUNT; ++i) {
        struct spawn_allocator_vector vector = spawn_allocator_vectors[i];
#ifdef LEANOS_FIXTURE_SPAWN_ALLOCATOR_STALE_CHILD
        /* Present the first accepted termination with the child in slot 0
           under the next generation: the state a kernel that reused a slot
           without retiring the old control word would hold. */
        if (!fixture_applied && vector.kind == 's' && vector.input[1] == 102 &&
            vector.reply == 0x10001 && vector.state[6] != 0) {
            vector.state[6] += UINT64_C(1) << 16;
            fixture_applied = 1;
        }
#endif
        (void)fixture_applied;
        uint64_t reply = reply_of(&vector);
        if (reply != vector.reply) return fail_vector(i, "reply", vector.reply, reply);
        uint64_t value = value_of(&vector);
        if (value != vector.value) return fail_vector(i, "value", vector.value, value);
        for (uint64_t index = 0; index < 13; ++index) {
            uint64_t word = next_of(&vector, index);
            if (word != vector.next[index]) return fail_vector(i, "next", vector.next[index], word);
        }
        if (vector.kind == 's') {
            if (reply == 0x10001) ++accepted;
            else if (reply >= 0xfe20 && reply <= 0xfe23) ++refused;
            else ++rejected;
        } else {
            if (reply == 0x01) ++accepted;
            else if (reply >= 0xff00) ++errors;
            else ++rejected;
        }
        printf("SPAWNALLOC/%u kind=%c reply=%llu value=%llu\n", i, vector.kind,
            (unsigned long long)reply, (unsigned long long)value);
    }
    printf("spawn-allocator vectors=%llu accepted=%llu rejected=%llu refused=%llu errors=%llu\n",
        (unsigned long long)SPAWN_ALLOCATOR_VECTOR_COUNT, accepted, rejected, refused, errors);
    puts("Hosted generated-C spawn-allocator replay passed");
    return lean_io_result_mk_ok(lean_box(0));
}

int main(int argc, char **argv) {
    argv = lean_setup_args(argc, argv);
    lean_initialize();
    lean_object *result = initialize_leanos_LeanOS_SpawnAllocatorWords(1);
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
