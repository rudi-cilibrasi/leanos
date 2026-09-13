#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"

static unsigned cases;

static uint64_t query(const uint64_t w[9],uint64_t word) {
    return leanos_qotom_entry_integration_query(
        w[0],w[1],w[2],w[3],w[4],w[5],w[6],w[7],w[8],word);
}

static int accepted(const uint64_t w[9]) {
    ++cases;
    return query(w,0)==1 && query(w,1)==1 && query(w,2)==0 &&
        query(w,3)==1 && query(w,4)==1 && query(w,5)==1 &&
        query(w,6)==0 && query(w,7)==1;
}

static int rejected(const uint64_t w[9]) {
    ++cases;
    return query(w,1)==2 && query(w,2)!=0 && query(w,3)==0 &&
        query(w,4)==0 && query(w,5)==0 && query(w,6)==0;
}

int main(void) {
    const uint64_t baseline[9]={2,1,UINT64_C(0x1a0000),
        UINT64_C(0x1a2000),UINT64_C(0x1a2000),1,15,1,1};
    if(!accepted(baseline))return 1;
    for(unsigned slot=0;slot<9;++slot) {
        uint64_t changed[9];
        for(unsigned i=0;i<9;++i)changed[i]=baseline[i];
        switch(slot) {
        case 0: changed[slot]=1;break;
        case 1: changed[slot]=0;break;
        case 2: changed[slot]|=1;break;
        case 3: changed[slot]=changed[2];break;
        case 4: changed[slot]=changed[2];break;
        case 5: case 7: case 8: changed[slot]=0;break;
        case 6: changed[slot]=14;break;
        }
        if(!rejected(changed)) {
            fprintf(stderr,"rejected entry case %u failed\n",slot);
            return 2;
        }
    }
    printf("Qotom entry integration boundary: %u cases PASS\n",cases);
    return 0;
}
