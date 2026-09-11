#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include "boundary-abi.h"
#include "cases.h"
#include "finish-cases.h"
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
extern void leanos_register_boundary_target(const char *, void *);
int main(void) {
    leanos_register_boundary_target("leanos_qotom_madt_stream_byte_step_query",
        (void *)(uintptr_t)&leanos_qotom_madt_stream_byte_step_query);
    leanos_register_boundary_target("leanos_qotom_madt_stream_finish_query",
        (void *)(uintptr_t)&leanos_qotom_madt_stream_finish_query);
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
            ++composed_cases;
        }
        printf("%s %"PRIu64" %"PRIu64"\n",cases[c].name,result[1],result[2]);
    }
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
    printf("composed parser/BSP cases %zu\n",composed_cases);
    return 0;
}
