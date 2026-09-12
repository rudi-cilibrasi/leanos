#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include "boundary-abi.h"
#include "cases.h"
#include "finish-cases.h"
#include "../include/qotom_bsp_consumer.h"
static uint64_t query(const uint64_t s[12], uint64_t length, uint64_t executing,
                      uint64_t offset, uint64_t byte, uint64_t word) {
    return leanos_qotom_madt_stream_byte_step_query(s[0],s[1],s[2],s[3],s[4],s[5],
        s[6],s[7],s[8],s[9],s[10],s[11],length,executing,offset,byte,word);
}
static uint64_t finish(const uint64_t a[20], uint64_t word) {
    return leanos_qotom_madt_stream_finish_query(a[0],a[1],a[2],a[3],a[4],a[5],
        a[6],a[7],a[8],a[9],a[10],a[11],a[12],a[13],a[14],a[15],a[16],a[17],
        a[18],a[19],word);
}
static uint64_t admission(const uint64_t a[12], uint64_t word) {
    return leanos_qotom_machine_topology_admission_result_query(
        a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],a[9],a[10],a[11],word);
}
static uint64_t nmi_policy(const uint64_t a[6], uint64_t word) {
    return leanos_qotom_madt_nmi_policy_query(
        a[0],a[1],a[2],a[3],a[4],a[5],word);
}
extern void leanos_register_boundary_target(const char *, void *);
int main(void) {
    leanos_register_boundary_target("leanos_qotom_madt_stream_byte_step_query",
        (void *)(uintptr_t)&leanos_qotom_madt_stream_byte_step_query);
    leanos_register_boundary_target("leanos_qotom_madt_stream_finish_query",
        (void *)(uintptr_t)&leanos_qotom_madt_stream_finish_query);
    leanos_register_boundary_target("leanos_qotom_madt_nmi_policy_query",
        (void *)(uintptr_t)&leanos_qotom_madt_nmi_policy_query);
    leanos_register_boundary_target("leanos_qotom_machine_topology_admission_result_query",
        (void *)(uintptr_t)&leanos_qotom_machine_topology_admission_result_query);
    const struct qotom_bsp_observation empty_observation = {0};
    const uint8_t one_byte = 0;
    if (qotom_bind_validated_madt_entries(NULL,1,&empty_observation).status != 1 ||
        qotom_bind_validated_madt_entries(&one_byte,1,NULL).status != 1 ||
        qotom_bind_validated_madt_entries(&one_byte,0,&empty_observation).status != 1 ||
        qotom_bind_validated_madt_entries(&one_byte,65536-43,&empty_observation).status != 1 ||
        qotom_bind_validated_madt_entries(&one_byte,SIZE_MAX,&empty_observation).status != 1)
        return 14;
    const uint64_t native_nmi[6] = {
        4,UINT64_C(0x0000f751dc010604),UINT64_C(0x0000a67499020604),
        UINT64_C(0x0000ce213a030604),UINT64_C(0x0000279e9d040604),0
    };
    const uint64_t accepted_nmi[6] = {1,1,0,1,4,0};
    for (uint64_t word = 0; word < 6; ++word)
        if (nmi_policy(native_nmi,word) != accepted_nmi[word]) return 18;
    if (nmi_policy(native_nmi,UINT64_MAX) != 0) return 19;
    for (size_t field = 0; field < 6; ++field) {
        uint64_t changed[6]; memcpy(changed,native_nmi,sizeof(changed));
        changed[field] ^= 1;
        const uint64_t error = field == 0 ? 87 : field == 5 ? 89 : 88;
        const uint64_t rejected[6] = {1,2,error,0,0,0};
        for (uint64_t word = 0; word < 6; ++word)
            if (nmi_policy(changed,word) != rejected[word]) return 20;
    }
    size_t composed_cases = 0;
    for (size_t c = 0; c < sizeof(cases)/sizeof(cases[0]); ++c) {
        uint64_t state[12] = {44,0,0,0,0,0,0,256,0,0,0,0};
        uint64_t result[18] = {0};
        for (size_t i = 0; i < cases[c].length; ++i) {
            for (uint64_t word = 0; word < 18; ++word)
                result[word] = query(state, 44+cases[c].length, cases[c].executing,
                                     44+i, cases[c].bytes[i], word);
            if (result[0] != 1 || result[16] != 0 || result[17] != 0 ||
                query(state,44+cases[c].length,cases[c].executing,44+i,
                      cases[c].bytes[i],UINT64_MAX) != 0) return 2;
            if (result[1] == 2) {
                for (size_t word = 3; word < 18; ++word)
                    if (result[word] != 0) return 3;
                break;
            }
            if (result[1] != (i+1 == cases[c].length ? 3u : 1u) ||
                result[2] != 0 || result[3] != 45+i ||
                result[15] != cases[c].bytes[i]) return 4;
            memcpy(state, result+3, sizeof(state));
        }
        uint64_t status = cases[c].error ? 2 : 3;
        if (result[1] != status || result[2] != cases[c].error) {
            fprintf(stderr,"%s: status=%"PRIu64" error=%"PRIu64"\n",
                    cases[c].name,result[1],result[2]);
            return 1;
        }
        if (status == 3 && (state[6] != 4 || state[7] != 0 || state[8] != 85 ||
                           state[9] || state[10] || state[11])) return 5;
        uint64_t bound[20] = {result[1],result[2]};
        memcpy(bound+2,result+3,12*sizeof(uint64_t));
        bound[14] = 44+cases[c].length; bound[15] = cases[c].executing;
        bound[16] = 0x220; bound[17] = 1; bound[18] = 0xfee00900; bound[19] = 0;
        const uint64_t accepted[6] = {1,1,0,4,0xfee00900,0};
        const uint64_t rejected[6] = {1,2,78,0,0,0};
        for (uint64_t word = 0; word < 6; ++word)
            if (finish(bound,word) != (status == 3 ? accepted[word] : rejected[word]))
                return 7;
        /* Compose actual parser projections with every independently checked
           BSP observation, including the manifest-pinned native observation.
           Shape mutations remain standalone probes below. */
        for (size_t observation = 0;
             observation < sizeof(finish_cases)/sizeof(finish_cases[0]);
             ++observation) {
            if (memcmp(finish_cases[observation].args, finish_cases[0].args,
                       16*sizeof(uint64_t)) != 0) continue;
            memcpy(bound+16, finish_cases[observation].args+16, 4*sizeof(uint64_t));
            for (uint64_t word = 0; word < 6; ++word) {
                const uint64_t expected = status == 3 ?
                    finish_cases[observation].words[word] : rejected[word];
                if (finish(bound,word) != expected) {
                    fprintf(stderr,"%s / %s: composed finish word=%"PRIu64"\n",
                            cases[c].name,finish_cases[observation].name,word);
                    return 10;
                }
            }
            struct qotom_bsp_observation obs = {cases[c].executing,
                bound[16],bound[17],bound[18],bound[19],0};
            struct qotom_bsp_result candidate = qotom_bind_validated_madt_entries(
                cases[c].bytes,cases[c].length,&obs);
            uint64_t want_status = status != 3 ? 2 :
                finish_cases[observation].words[1] == 1 ? 0 : 4;
            if (candidate.status != want_status) return 11;
            if (!candidate.status) {
                if (candidate.apic_id != finish_cases[observation].words[2] ||
                    candidate.processor_count != finish_cases[observation].words[3] ||
                    candidate.apic_base != finish_cases[observation].words[4] ||
                    candidate.offset != 44+cases[c].length) return 12;
            } else {
                uint64_t detail = status != 3 ? cases[c].error :
                    finish_cases[observation].words[2];
                if (candidate.detail != detail || candidate.apic_id ||
                    candidate.processor_count || candidate.apic_base) return 13;
            }
            ++composed_cases;
        }
        printf("%s %"PRIu64" %"PRIu64"\n",cases[c].name,result[1],result[2]);
    }
    /* The scalar entry stream deliberately retains opaque type-4 bytes.  The
       composed consumer must reject drift in each routing field, a missing
       record, and any caller request to use the malformed records. */
    if (cases[0].length > 256u) return 21;
    size_t nmi_offsets[4], nmi_count = 0;
    for (size_t offset = 0; offset < cases[0].length;) {
        size_t length = cases[0].bytes[offset+1u];
        if (cases[0].bytes[offset] == 4u && nmi_count < 4u)
            nmi_offsets[nmi_count++] = offset;
        offset += length;
    }
    if (nmi_count != 4) return 22;
    const struct qotom_bsp_observation native_observation = {
        0,0x220,1,0xfee00900,0,0
    };
    for (size_t record = 0; record < 4; ++record) {
        for (size_t byte = 2; byte < 6; ++byte) {
            uint8_t changed[256];
            memcpy(changed,cases[0].bytes,cases[0].length);
            changed[nmi_offsets[record]+byte] ^= 1;
            struct qotom_bsp_result result = qotom_bind_validated_madt_entries(
                changed,cases[0].length,&native_observation);
            if (result.status != 5 || result.detail != 88 ||
                result.offset != 44u+cases[0].length) return 23;
        }
    }
    uint8_t missing[256];
    const size_t removed = nmi_offsets[3];
    memcpy(missing,cases[0].bytes,removed);
    memcpy(missing+removed,cases[0].bytes+removed+6,
           cases[0].length-removed-6);
    struct qotom_bsp_result result = qotom_bind_validated_madt_entries(
        missing,cases[0].length-6,&native_observation);
    if (result.status != 5 || result.detail != 87 ||
        result.offset != 44u+cases[0].length-6u) return 24;
    struct qotom_bsp_observation routing_observation = native_observation;
    routing_observation.interrupt_routing_authority = 1;
    result = qotom_bind_validated_madt_entries(
        cases[0].bytes,cases[0].length,&routing_observation);
    if (result.status != 5 || result.detail != 89 ||
        result.offset != 44u+cases[0].length) return 25;
    for (size_t p = 0; p < sizeof(probes)/sizeof(probes[0]); ++p) {
        const uint64_t *a = probes[p].args;
        for (uint64_t word = 0; word < 18; ++word) {
            const uint64_t expected = word == 0 ? 1 : word == 1 ? 2 :
                                      word == 2 ? probes[p].error : 0;
            if (query(a,a[12],a[13],a[14],a[15],word) != expected) {
                fprintf(stderr,"%s: word=%"PRIu64"\n",probes[p].name,word);
                return 6;
            }
        }
        printf("%s 2 %"PRIu64"\n",probes[p].name,probes[p].error);
    }
    for (size_t c = 0; c < sizeof(finish_cases)/sizeof(finish_cases[0]); ++c) {
        for (uint64_t word = 0; word < 6; ++word)
            if (finish(finish_cases[c].args,word) != finish_cases[c].words[word]) {
                fprintf(stderr,"%s: finish word=%"PRIu64"\n",finish_cases[c].name,word);
                return 8;
            }
        if (finish(finish_cases[c].args,UINT64_MAX) != 0) return 9;
        printf("finish %s OK\n",finish_cases[c].name);
    }
    const uint64_t accepted_admission[12] = {
        2,0xb979f078,0xb979f078,10,10,1,0,0,0,4,0xfee00900,0
    };
    static const struct {
        const char *name;
        size_t field;
        uint64_t value, error;
    } admission_cases[] = {
        {"root-kind",0,0,80}, {"root-address",1,0,80},
        {"root-copy",2,0xb979f028,80}, {"advertised-zero",3,0,81},
        {"advertised-overflow",3,257,81}, {"copy-incomplete",4,9,81},
        {"madt-missing",5,0,82}, {"madt-duplicate",5,2,82},
        {"consumer-rejected",6,4,83}, {"consumer-detail",7,22,83},
        {"admitted-width",8,256,84}, {"admitted-nonzero",8,2,84},
        {"executing-mismatch",11,2,84}, {"processor-count",9,1,85},
        {"apic-base",10,0xfee00000,86},
    };
    const uint64_t accepted_words[4] = {1,1,0,0};
    for (uint64_t word = 0; word < 4; ++word)
        if (admission(accepted_admission,word) != accepted_words[word]) return 15;
    if (admission(accepted_admission,UINT64_MAX) != 0) return 16;
    for (size_t c = 0; c < sizeof(admission_cases)/sizeof(admission_cases[0]); ++c) {
        uint64_t input[12];
        memcpy(input,accepted_admission,sizeof(input));
        input[admission_cases[c].field] = admission_cases[c].value;
        const uint64_t rejected_words[4] = {1,2,admission_cases[c].error,0};
        for (uint64_t word = 0; word < 4; ++word)
            if (admission(input,word) != rejected_words[word]) return 17;
        printf("admission %s rejected=%"PRIu64"\n",
               admission_cases[c].name,admission_cases[c].error);
    }
    printf("composed parser/BSP cases %zu\n",composed_cases);
    return 0;
}
