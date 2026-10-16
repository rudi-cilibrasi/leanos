#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"

/* Slot 0 is the inventory variant (LeanOS.QotomCopyRootPublication): 0 is
 * the ordinary five-frame inventory, 1 the DHCP-subject six-frame inventory
 * (issue #556), 2 the production eight-frame inventory (issue #569). Each
 * variant must accept exactly its own counts and reject the others'. */
enum { SLOTS = 13 };

static unsigned cases;

static uint64_t query(const uint64_t w[SLOTS],uint64_t word) {
    return leanos_qotom_copy_root_publication_query(
        w[0],w[1],w[2],w[3],w[4],w[5],w[6],w[7],w[8],w[9],w[10],w[11],w[12],
        word);
}

static int accepted(const uint64_t w[SLOTS]) {
    ++cases;
    return query(w,0)==2 && query(w,1)==1 && query(w,2)==0 &&
        query(w,3)==1 && query(w,4)==1 && query(w,5)==16 &&
        query(w,6)==0 && query(w,7)==1;
}

static int rejected(const uint64_t w[SLOTS]) {
    ++cases;
    return query(w,1)==2 && query(w,2)!=0 && query(w,3)==0 &&
        query(w,4)==0 && query(w,5)==0 && query(w,6)==0;
}

static int rejected_with(const uint64_t w[SLOTS],uint64_t mask) {
    return rejected(w) && query(w,2)==mask;
}

static void copy(uint64_t out[SLOTS],const uint64_t in[SLOTS]) {
    for(unsigned i=0;i<SLOTS;++i)out[i]=in[i];
}

/* Every single-slot mutation of an accepted vector is rejected. */
static int mutations(const uint64_t baseline[SLOTS],const char *name) {
    for(unsigned slot=0;slot<SLOTS;++slot) {
        uint64_t changed[SLOTS];
        copy(changed,baseline);
        switch(slot) {
        case 0: changed[slot]=baseline[0]==2?3:2;break;
        case 1: changed[slot]=1;break;
        case 2: changed[slot]=baseline[2]+1;break;
        case 3: changed[slot]=baseline[3]==3?2:5;break;
        case 4: changed[slot]=baseline[4]-1;break;
        case 5: changed[slot]=1;break;
        case 6: changed[slot]|=1;break;
        case 7: changed[slot]=changed[6];break;
        case 8: case 9: case 11: changed[slot]=0;break;
        case 10: changed[slot]=15;break;
        case 12: changed[slot]=changed[7];break;
        }
        if(!rejected(changed)) {
            fprintf(stderr,"%s: rejected publication case %u failed\n",name,slot);
            return 0;
        }
    }
    return 1;
}

int main(void) {
    const uint64_t base[SLOTS]={0,0,5,3,4088,2,UINT64_C(0x300000),
        UINT64_C(0x30b000),1,1,16,1,UINT64_C(0x300000)};
    const uint64_t dhcp[SLOTS]={1,0,6,4,4087,2,UINT64_C(0x300000),
        UINT64_C(0x30b000),1,1,16,1,UINT64_C(0x300000)};
    const uint64_t production[SLOTS]={2,0,8,4,4085,2,UINT64_C(0x300000),
        UINT64_C(0x30b000),1,1,16,1,UINT64_C(0x300000)};
    if(!accepted(base) || !accepted(dhcp) || !accepted(production))return 1;
    if(!mutations(base,"base") || !mutations(dhcp,"dhcp-subject") ||
       !mutations(production,"production"))return 2;

    /* Each variant rejects the other's inventory, whole or in part. The
     * first case is the hardware-observed DHCP-subject inventory checked
     * against the five-frame counts (error mask 6). */
    uint64_t w[SLOTS];
    copy(w,dhcp);w[0]=0;
    if(!rejected_with(w,6))return 3;
    copy(w,base);w[0]=1;
    if(!rejected_with(w,6))return 4;
    copy(w,base);w[2]=6;
    if(!rejected_with(w,2))return 5;
    copy(w,base);w[3]=4;w[4]=4087;
    if(!rejected_with(w,4))return 6;
    copy(w,dhcp);w[2]=5;
    if(!rejected_with(w,2))return 7;
    copy(w,dhcp);w[3]=3;w[4]=4088;
    if(!rejected_with(w,4))return 8;
    /* The production variant rejects the other two inventories, and they
     * reject its counts. */
    copy(w,base);w[0]=2;
    if(!rejected_with(w,6))return 13;
    copy(w,dhcp);w[0]=2;
    if(!rejected_with(w,6))return 14;
    copy(w,production);w[0]=0;
    if(!rejected_with(w,6))return 15;
    copy(w,production);w[0]=1;
    if(!rejected_with(w,6))return 16;
    /* A range of variants is not accepted: only 0, 1 and 2 exist. */
    for(uint64_t variant=3;variant<8;++variant) {
        copy(w,base);w[0]=variant;
        if(!rejected_with(w,2048|6))return 10;
        copy(w,dhcp);w[0]=variant;
        if(!rejected_with(w,2048|6))return 11;
        copy(w,production);w[0]=variant;
        if(!rejected_with(w,2048|6))return 17;
    }
    copy(w,base);w[0]=UINT64_MAX;
    if(!rejected_with(w,2048|6))return 12;
    printf("Qotom copy-root publication boundary: %u cases PASS\n",cases);
    return 0;
}
