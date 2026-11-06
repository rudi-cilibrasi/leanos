#ifndef LEANOS_QOTOM_BSP_CONSUMER_H
#define LEANOS_QOTOM_BSP_CONSUMER_H
#include <stddef.h>
#include <stdint.h>
#include "boundary-abi.h"

/* Candidate only. Caller owns an immutable, root-selected, envelope-validated
 * MADT copy and an authoritative observation from the executing CPU. The
 * explicit production candidate supplies those inputs and separately binds
 * this result to its root/copy/publication state. It recognizes the exact
 * malformed type-4 records only under disabled routing authority; neither AP
 * dormancy, hardware LVT state nor platform admission follows from it.
 * entries points after the 44-byte fixed header, with exactly length bytes. */
struct qotom_bsp_observation {
    uint64_t executing, cpuid_edx, available, apic_base, sample_id;
    /* Zero means the caller will not interpret MADT type-4 records or program
       local-APIC routing from them. */
    uint64_t interrupt_routing_authority;
};
struct qotom_bsp_result {
    /* 0: candidate bound; 1: input bounds; 2: stream rejection;
       3: ABI inconsistency; 4: BSP binding rejection;
       5: malformed native NMI routing was not quarantined. */
    uint64_t status, detail, offset;
    uint64_t apic_id, processor_count, apic_base;
};
/* Write a result and return its status. */
static inline uint64_t qotom_bsp_publish(struct qotom_bsp_result *out,
        uint64_t status, uint64_t detail, uint64_t offset, uint64_t apic_id,
        uint64_t processor_count, uint64_t apic_base) {
    out->status = status; out->detail = detail; out->offset = offset;
    out->apic_id = apic_id; out->processor_count = processor_count;
    out->apic_base = apic_base;
    return status;
}
/* Writes the result through `out` and returns its status; a NULL `out` is an
 * input-bounds rejection with nothing written (#608: no struct is returned by
 * value or copied, so QuickProof's clightgen and VST can take this function). */
static inline uint64_t qotom_bind_validated_madt_entries(
        const uint8_t *entries, size_t length,
        const struct qotom_bsp_observation *observation,
        struct qotom_bsp_result *out) {
    if (!out) return 1;
    if (!entries || !observation || !length || length > 65536u - 44u)
        return qotom_bsp_publish(out,1,0,44,0,0,0);
    /* The observation is read once, here. */
    const uint64_t executing = observation->executing,
        cpuid_edx = observation->cpuid_edx,
        available = observation->available,
        apic_base = observation->apic_base,
        sample_id = observation->sample_id,
        routing_authority = observation->interrupt_routing_authority;
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
                table_length,executing,offset,byte,word);
        if (result[0] != 1) return qotom_bsp_publish(out,3,0,offset,0,0,0);
        if (result[1] == 2)
            return qotom_bsp_publish(out,2,result[2],offset,0,0,0);
        if (result[1] != (i + 1 == length ? 3u : 1u) ||
            result[2] || result[3] != offset + 1 || result[15] != byte)
            return qotom_bsp_publish(out,3,0,offset,0,0,0);
        for (size_t word = 0; word < 12; ++word) state[word] = result[word+3];
    }
    uint64_t nmi[4] = {0,0,0,0}, nmi_count = 0;
    for (size_t offset = 0; offset < length;) {
        if (length - offset < 2u) return qotom_bsp_publish(out,3,0,state[0],0,0,0);
        const size_t record_length = entries[offset+1u];
        if (record_length < 2u || record_length > length - offset)
            return qotom_bsp_publish(out,3,0,state[0],0,0,0);
        if (entries[offset] == 4u) {
            if (record_length != 6u) return qotom_bsp_publish(out,3,0,state[0],0,0,0);
            uint64_t packed = 0;
            for (size_t byte = 0; byte < 6u; ++byte)
                packed |= (uint64_t)entries[offset+byte] << (8u*byte);
            if (nmi_count < 4u) nmi[nmi_count] = packed;
            ++nmi_count;
        }
        offset += record_length;
    }
    uint64_t nmi_policy[5];
    for (uint64_t word = 0; word < 5; ++word)
        nmi_policy[word] = leanos_qotom_madt_nmi_policy_query(
            nmi_count,nmi[0],nmi[1],nmi[2],nmi[3],routing_authority,word);
    if (nmi_policy[0] != 1 || nmi_policy[3] > 1 || nmi_policy[4] > 4)
        return qotom_bsp_publish(out,3,0,state[0],0,0,0);
    if (nmi_policy[1] != 1)
        return qotom_bsp_publish(out,5,nmi_policy[2],state[0],0,0,0);
    if (nmi_policy[2] || nmi_policy[3] != 1 || nmi_policy[4] != 4)
        return qotom_bsp_publish(out,3,0,state[0],0,0,0);
    uint64_t bound[6];
    for (uint64_t word = 0; word < 6; ++word)
        bound[word] = leanos_qotom_madt_stream_finish_query(
            result[1],result[2],state[0],state[1],state[2],state[3],state[4],
            state[5],state[6],state[7],state[8],state[9],state[10],state[11],
            table_length,executing,cpuid_edx,available,apic_base,sample_id,
            word);
    if (bound[0] != 1 || bound[5] != 0)
        return qotom_bsp_publish(out,3,0,state[0],0,0,0);
    if (bound[1] == 2 || bound[1] == 5)
        return qotom_bsp_publish(out,4,bound[2],state[0],0,0,0);
    if (bound[1] != 1 || bound[2] != executing ||
        bound[3] != state[6] || bound[4] != apic_base)
        return qotom_bsp_publish(out,3,0,state[0],0,0,0);
    return qotom_bsp_publish(out,0,0,state[0],bound[2],bound[3],bound[4]);
}
#endif
