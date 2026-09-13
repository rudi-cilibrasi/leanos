#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"
extern void leanos_register_boundary_target(const char *, void *);

static unsigned cases;

static uint64_t query(const uint64_t w[15],uint64_t word) {
    return leanos_qotom_blocking_ipc_integration_query(
        w[0],w[1],w[2],w[3],w[4],w[5],w[6],w[7],w[8],w[9],
        w[10],w[11],w[12],w[13],w[14],word);
}

static int accepted(const uint64_t w[15]) {
    ++cases;
    static const uint64_t expected[11]={1,1,0,1,8,1,2,2,4,4,1};
    for(uint64_t word=0;word<11;++word)
        if(query(w,word)!=expected[word])return 0;
    return query(w,11)==0 && query(w,UINT64_MAX)==0;
}

static int rejected(const uint64_t w[15],uint64_t error) {
    ++cases;
    return query(w,0)==1 && query(w,1)==2 && query(w,2)==error &&
        query(w,3)==0 && query(w,4)==0 && query(w,5)==0 &&
        query(w,6)==0 && query(w,7)==0 && query(w,8)==0 &&
        query(w,9)==0 && query(w,10)==0;
}

int main(void) {
    leanos_register_boundary_target(
        "leanos_qotom_blocking_ipc_integration_query",
        (void *)(uintptr_t)&leanos_qotom_blocking_ipc_integration_query);
    const uint64_t baseline[15]={1,1,1,UINT64_C(0x1a0000),
        UINT64_C(0x1b0000),UINT64_C(0x1c0000),1,1,1,1,1,1,1,2,1};
    static const uint64_t errors[15]={1,2,4,8,16,32,64,64,64,
        128,128,256,256,512,1024};
    if(!accepted(baseline))return 1;
    for(unsigned slot=0;slot<15;++slot) {
        uint64_t changed[15];
        for(unsigned i=0;i<15;++i)changed[i]=baseline[i];
        switch(slot) {
        case 0: case 1: case 2: case 6: case 7: case 8:
        case 9: case 10: case 11: case 12: case 14:
            changed[slot]=0;break;
        case 3: changed[slot]|=1;break;
        case 4: changed[slot]=changed[3];break;
        case 5: changed[slot]=changed[4];break;
        case 13: changed[slot]=1;break;
        }
        if(!rejected(changed,errors[slot])) {
            fprintf(stderr,"rejected Qotom blocking IPC case %u failed\n",slot);
            return 2;
        }
    }
    printf("Qotom blocking IPC integration boundary: %u cases PASS\n",cases);
    return 0;
}
