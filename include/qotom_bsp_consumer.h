#ifndef LEANOS_QOTOM_BSP_CONSUMER_H
#define LEANOS_QOTOM_BSP_CONSUMER_H
#include <stddef.h>
#include <stdint.h>
#include "boundary-abi.h"

/* Candidate only. Caller owns an immutable, root-selected, envelope-validated
 * MADT copy and an authoritative observation from the executing CPU. The
 * explicit production candidate supplies those inputs and separately binds
 * this result to its root/copy/publication state. Neither AP dormancy nor
 * interrupt routing nor platform admission follows from this consumer.
 * entries points after the 44-byte fixed header, with exactly length bytes. */
struct qotom_bsp_observation {
    uint64_t executing, cpuid_edx, available, apic_base, sample_id;
};
struct qotom_bsp_result {
    /* 0: candidate bound; 1: input bounds; 2: stream rejection;
       3: ABI inconsistency; 4: BSP binding rejection. */
    uint64_t status, detail, offset;
    uint64_t apic_id, processor_count, apic_base;
};
static inline struct qotom_bsp_result qotom_bind_validated_madt_entries(
        const uint8_t *entries, size_t length,
        const struct qotom_bsp_observation *observation) {
    struct qotom_bsp_result out = {1,0,44,0,0,0};
    if (!entries || !observation || !length || length > 65536u - 44u)
        return out;
    const struct qotom_bsp_observation obs = *observation;
    uint64_t state[12] = {44,0,0,0,0,0,0,256,0,0,0,0};
    uint64_t result[16] = {0};
    const uint64_t table_length = 44u + length;
    for (size_t i = 0; i < length; ++i) {
        const uint64_t byte = entries[i], offset = 44u + i;
        /* Every projection sees the same old state and byte. */
        for (uint64_t word = 0; word < 16; ++word)
            result[word] = leanos_qotom_madt_stream_byte_step_query(
                state[0],state[1],state[2],state[3],state[4],state[5],
                state[6],state[7],state[8],state[9],state[10],state[11],
                table_length,obs.executing,offset,byte,word);
        out.offset = offset;
        if (result[0] != 1) { out.status = 3; return out; }
        if (result[1] == 2) {
            out.status = 2; out.detail = result[2]; return out;
        }
        if (result[1] != (i + 1 == length ? 3u : 1u) ||
            result[2] || result[3] != offset + 1 || result[15] != byte) {
            out.status = 3; return out;
        }
        for (size_t word = 0; word < 12; ++word) state[word] = result[word+3];
    }
    uint64_t bound[6];
    for (uint64_t word = 0; word < 6; ++word)
        bound[word] = leanos_qotom_madt_stream_finish_query(
            result[1],result[2],state[0],state[1],state[2],state[3],state[4],
            state[5],state[6],state[7],state[8],state[9],state[10],state[11],
            table_length,obs.executing,obs.cpuid_edx,obs.available,
            obs.apic_base,obs.sample_id,word);
    out.offset = state[0];
    if (bound[0] != 1 || bound[5] != 0) { out.status = 3; return out; }
    if (bound[1] == 2 || bound[1] == 5) {
        out.status = 4; out.detail = bound[2]; return out;
    }
    if (bound[1] != 1 || bound[2] != obs.executing ||
        bound[3] != state[6] || bound[4] != obs.apic_base) {
        out.status = 3; return out;
    }
    out.status = 0;
    out.apic_id = bound[2]; out.processor_count = bound[3];
    out.apic_base = bound[4];
    return out;
}
#endif
