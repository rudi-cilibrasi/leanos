#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"
extern void leanos_register_boundary_target(const char *, void *);

static unsigned cases;

static uint64_t query(const uint64_t w[23], uint64_t word) {
    return leanos_platform_admission_query(
        w[0],w[1],w[2],w[3],w[4],w[5],w[6],w[7],w[8],w[9],w[10],
        w[11],w[12],w[13],w[14],w[15],w[16],w[17],w[18],w[19],
        w[20],w[21],w[22],word);
}

static int accepted(const uint64_t w[23], uint64_t profile,
        uint64_t debug_exit) {
    ++cases;
    const uint64_t expected[8]={1,1,0,profile,1,1,debug_exit,0};
    for(uint64_t word=0;word<8;++word)
        if(query(w,word)!=expected[word])return 0;
    return query(w,8)==0 && query(w,UINT64_MAX)==0;
}

static int rejected(const uint64_t w[23], uint64_t reason) {
    ++cases;
    if(query(w,0)!=1 || query(w,1)!=0 || query(w,2)!=reason)return 0;
    for(uint64_t word=3;word<9;++word)if(query(w,word)!=0)return 0;
    return 1;
}

static void copy_words(uint64_t out[23],const uint64_t in[23]) {
    for(unsigned i=0;i<23;++i)out[i]=in[i];
}

int main(void) {
    leanos_register_boundary_target("leanos_platform_admission_query",
        (void *)(uintptr_t)&leanos_platform_admission_query);
    static const uint64_t q35[23]={
        1,1,0x351,1,0x352,1,0x353,1,0x3f8,38400,1,
        0x354,1,0,1,0,0x355,1,1,1,10,1,1};
    static const uint64_t qotom[23]={
        2,2,0x1901,1,0x1902,1,0x1903,1,0x3f8,38400,1,
        0x1904,1,0,4,0,0x1905,1,0,0,10,1,1};
    if(!accepted(q35,1,1) || !accepted(qotom,2,0))return 1;

    uint64_t changed[23];
    copy_words(changed,qotom);changed[0]=99;
    if(!rejected(changed,1))return 2;
    copy_words(changed,qotom);changed[1]=1;
    if(!rejected(changed,2))return 3;

    static const unsigned slots[]={2,3,4,5,6,7,8,9,10,11,12,13,14,15,
        16,17,18,19,20,21,22};
    static const uint64_t reasons[]={3,3,4,4,5,5,6,6,6,7,7,7,7,8,
        9,9,10,10,11,11,12};
    for(unsigned i=0;i<sizeof(slots)/sizeof(slots[0]);++i) {
        copy_words(changed,qotom);
        changed[slots[i]]^=1;
        if(!rejected(changed,reasons[i])) {
            fprintf(stderr,"platform rejection slot %u expected reason %" PRIu64 "\n",
                slots[i],reasons[i]);
            return 4;
        }
    }

    /* Direct q35/Qotom component splices must retain typed rejection. */
    static const unsigned component_slots[]={2,4,6,11,14,16,18,19};
    for(unsigned i=0;i<sizeof(component_slots)/sizeof(component_slots[0]);++i) {
        unsigned slot=component_slots[i];
        copy_words(changed,qotom);changed[slot]=q35[slot];
        if(!rejected(changed,
            slot==2?3:slot==4?4:slot==6?5:slot==11||slot==14?7:
            slot==16?9:10))return 5;
    }
    printf("Platform admission boundary: %u cases PASS\n",cases);
    return 0;
}
