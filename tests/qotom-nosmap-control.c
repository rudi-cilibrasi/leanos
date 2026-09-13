#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"

static unsigned cases;

static uint64_t query(const uint64_t w[5], uint64_t word) {
    return leanos_qotom_nosmap_control_query(
        w[0],w[1],w[2],w[3],w[4],word);
}

static int accepted(const uint64_t w[5]) {
    ++cases;
    if(query(w,0)!=1 || query(w,1)!=1 || query(w,2)!=1 || query(w,3)!=0 ||
       query(w,4)!=1 || query(w,5)!=16 || query(w,6)!=2 || query(w,7)!=1 ||
       query(w,8)!=0 || query(w,9)!=0 || query(w,10)!=0 || query(w,11)!=0) {
        fprintf(stderr,"accepted no-SMAP case %u failed\n",cases);
        return 0;
    }
    return 1;
}

static int rejected(const uint64_t w[5], int precondition) {
    ++cases;
    if(query(w,1)!=(precondition?1u:2u) || query(w,2)!=2 || query(w,3)==0 ||
       query(w,8)!=0 || query(w,9)!=0 || query(w,10)!=0) {
        fprintf(stderr,"rejected no-SMAP case %u failed\n",cases);
        return 0;
    }
    return 1;
}

int main(void) {
    const uint64_t baseline[5]={UINT64_C(0x8001003b),UINT64_C(0x20),
        UINT64_C(0x100020),UINT64_C(0xd00),UINT64_C(0x2)};
    if(!accepted(baseline))return 1;
    uint64_t changed[5];
    for(unsigned i=0;i<5;++i)changed[i]=baseline[i];
    changed[1]|=UINT64_C(0x100000);changed[2]=changed[1];
    if(!accepted(changed))return 1;

    const struct { unsigned slot; uint64_t bit; } pre[]={{0,UINT64_C(0x10000)},
        {3,UINT64_C(0x800)},{1,UINT64_C(0x200000)},
        {1,UINT64_C(0x20000)},{1,UINT64_C(0x80)},{4,UINT64_C(0x200)}};
    for(unsigned i=0;i<sizeof(pre)/sizeof(pre[0]);++i) {
        for(unsigned j=0;j<5;++j)changed[j]=baseline[j];
        changed[pre[i].slot]^=pre[i].bit;
        if(!rejected(changed,0))return 1;
    }
    for(unsigned variant=0;variant<3;++variant) {
        for(unsigned j=0;j<5;++j)changed[j]=baseline[j];
        if(variant==0)changed[2]=changed[1];
        if(variant==1)changed[2]|=UINT64_C(0x200000);
        if(variant==2)changed[2]|=UINT64_C(0x40);
        if(!rejected(changed,1))return 1;
    }
    puts("PASS Qotom no-SMAP control boundary: 11 cases");
    return 0;
}
