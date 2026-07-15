#include <stdint.h>
#include <stdio.h>
#include "corpus.h"

extern uint64_t leanos_boot_transition(uint64_t, uint64_t);
extern uint64_t leanos_syscall_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_ipc_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_preemption_demo(uint64_t, uint64_t, uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t left, uint64_t right) { return left == right; }

int main(void) {
    for (unsigned i = 0; i < ORACLE_VECTOR_COUNT; ++i) {
        const struct oracle_vector *v = &oracle_vectors[i];
        uint64_t got = v->adapter == 0
            ? leanos_boot_transition(v->words[0], v->words[1])
            : v->adapter == 1
                ? leanos_syscall_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                : v->adapter == 2
                    ? leanos_ipc_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                    : leanos_preemption_demo(v->words[0], v->words[1], v->words[2], v->words[3]);
        if (got != v->expected) {
            fprintf(stderr, "oracle mismatch: %u %s expected=%llu got=%llu\n", i, v->id,
                v->expected, (unsigned long long)got);
            return 1;
        }
        printf("ORACLE/%u id=%s result=%llu\n", i, v->id, (unsigned long long)got);
    }
    return 0;
}
