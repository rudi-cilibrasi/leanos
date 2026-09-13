#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"

static unsigned cases;

static uint64_t query(const uint64_t w[12],uint64_t word) {
    return leanos_qotom_copy_root_publication_query(
        w[0],w[1],w[2],w[3],w[4],w[5],w[6],w[7],w[8],w[9],w[10],w[11],word);
}

static int accepted(const uint64_t w[12]) {
    ++cases;
    return query(w,0)==1 && query(w,1)==1 && query(w,2)==0 &&
        query(w,3)==1 && query(w,4)==1 && query(w,5)==16 &&
        query(w,6)==0 && query(w,7)==1;
}

static int rejected(const uint64_t w[12]) {
    ++cases;
    return query(w,1)==2 && query(w,2)!=0 && query(w,3)==0 &&
        query(w,4)==0 && query(w,5)==0 && query(w,6)==0;
}

int main(void) {
    const uint64_t baseline[12]={0,5,3,4088,2,UINT64_C(0x300000),
        UINT64_C(0x30b000),1,1,16,1,UINT64_C(0x300000)};
    if(!accepted(baseline))return 1;
    for(unsigned slot=0;slot<12;++slot) {
        uint64_t changed[12];
        for(unsigned i=0;i<12;++i)changed[i]=baseline[i];
        switch(slot) {
        case 0: changed[slot]=1;break;
        case 1: changed[slot]=4;break;
        case 2: changed[slot]=2;break;
        case 3: changed[slot]=4087;break;
        case 4: changed[slot]=1;break;
        case 5: changed[slot]|=1;break;
        case 6: changed[slot]=changed[5];break;
        case 7: case 8: case 10: changed[slot]=0;break;
        case 9: changed[slot]=15;break;
        case 11: changed[slot]=changed[6];break;
        }
        if(!rejected(changed)) {
            fprintf(stderr,"rejected publication case %u failed\n",slot);
            return 2;
        }
    }
    printf("Qotom copy-root publication boundary: %u cases PASS\n",cases);
    return 0;
}
