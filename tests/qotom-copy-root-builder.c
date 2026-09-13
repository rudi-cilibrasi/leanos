#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "qotom_copy_root_builder.h"

static struct qotom_root_pages source,closed,copy;
static struct qotom_root_build_result result;
static const uint64_t protected_frames[2]={3,4};
static const struct qotom_copy_alias aliases[2]={{100,3,0},{101,4,1}};
static unsigned cases;

static void initialize(void) {
    memset(&source,0,sizeof(source));
    source.pml4[0]=(uintptr_t)source.pdpt|7u;
    source.pdpt[0]=(uintptr_t)source.pd|7u;
    for(unsigned i=0;i<QOTOM_ROOT_PT_PAGES;++i)
        source.pd[i]=(uintptr_t)&source.pt[i*512u]|7u;
    for(unsigned i=0;i<QOTOM_ROOT_LEAVES;++i)
        source.pt[i]=(uint64_t)i<<12|QOTOM_ROOT_PRESENT|
            QOTOM_ROOT_WRITABLE|QOTOM_ROOT_NX;
    source.pt[100]=source.pt[101]=0;
    source.pt[200]=(UINT64_C(3)<<12)|QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX;
    source.pt[201]=(UINT64_C(4)<<12)|QOTOM_ROOT_PRESENT|
        QOTOM_ROOT_WRITABLE|QOTOM_ROOT_USER|QOTOM_ROOT_NX;
    memset(&closed,0xa5,sizeof(closed));memset(&copy,0x5a,sizeof(copy));
    memset(&result,0x3c,sizeof(result));
}

static int accepted(void) {
    ++cases;initialize();
    if(qotom_build_copy_roots(&source,&closed,&copy,protected_frames,2,
            aliases,2,&result)!=QOTOM_ROOT_BUILD_OK)return 0;
    if(result.protected_count!=2 || result.removed_aliases!=4 ||
       result.retained_present!=4090 || result.alias_count!=2)return 0;
    for(unsigned page=0;page<QOTOM_ROOT_LEAVES;++page) {
        uint64_t a=closed.pt[page],b=copy.pt[page];
        if((a&QOTOM_ROOT_PRESENT) &&
           ((a&QOTOM_ROOT_ADDRESS_MASK)==(UINT64_C(3)<<12) ||
            (a&QOTOM_ROOT_ADDRESS_MASK)==(UINT64_C(4)<<12)))return 0;
        if(page!=100 && page!=101 && a!=b)return 0;
    }
    return copy.pt[100]==((UINT64_C(3)<<12)|QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX) &&
           copy.pt[101]==((UINT64_C(4)<<12)|QOTOM_ROOT_PRESENT|
                          QOTOM_ROOT_WRITABLE|QOTOM_ROOT_NX);
}

static int rejected(enum qotom_root_build_status expected,
        const struct qotom_root_pages *s,struct qotom_root_pages *a,
        struct qotom_root_pages *b,const uint64_t *frames,size_t frame_count,
        const struct qotom_copy_alias *map,size_t map_count,
        struct qotom_root_build_result *record) {
    ++cases;
    unsigned char before_source[sizeof(source)];
    unsigned char before_closed[sizeof(closed)],before_copy[sizeof(copy)];
    struct qotom_root_build_result before_result=result;
    memcpy(before_source,&source,sizeof(source));
    memcpy(before_closed,&closed,sizeof(closed));memcpy(before_copy,&copy,sizeof(copy));
    enum qotom_root_build_status got=qotom_build_copy_roots(
        s,a,b,frames,frame_count,map,map_count,record);
    return got==expected && !memcmp(before_source,&source,sizeof(source)) &&
        !memcmp(before_closed,&closed,sizeof(closed)) &&
        !memcmp(before_copy,&copy,sizeof(copy)) &&
        !memcmp(&before_result,&result,sizeof(result));
}

int main(void) {
    if(!accepted())return 1;
    initialize();source.pml4[0]^=4096;
    if(!rejected(QOTOM_ROOT_BUILD_SOURCE,&source,&closed,&copy,
            protected_frames,2,aliases,2,&result))return 2;
    initialize();source.pd[0]|=UINT64_C(0x80);
    if(!rejected(QOTOM_ROOT_BUILD_SOURCE,&source,&closed,&copy,
            protected_frames,2,aliases,2,&result))return 3;
    initialize();uint64_t duplicate[2]={3,3};
    if(!rejected(QOTOM_ROOT_BUILD_PROTECTED,&source,&closed,&copy,
            duplicate,2,aliases,2,&result))return 4;
    initialize();struct qotom_copy_alias occupied[2]={{99,3,0},{101,4,0}};
    if(!rejected(QOTOM_ROOT_BUILD_ALIAS,&source,&closed,&copy,
            protected_frames,2,occupied,2,&result))return 5;
    initialize();struct qotom_copy_alias foreign[2]={{100,3,0},{101,5,0}};
    if(!rejected(QOTOM_ROOT_BUILD_ALIAS,&source,&closed,&copy,
            protected_frames,2,foreign,2,&result))return 6;
    initialize();struct qotom_copy_alias same_slot[2]={{100,3,0},{100,4,0}};
    if(!rejected(QOTOM_ROOT_BUILD_ALIAS,&source,&closed,&copy,
            protected_frames,2,same_slot,2,&result))return 7;
    initialize();
    if(!rejected(QOTOM_ROOT_BUILD_STORAGE,&source,&closed,&closed,
            protected_frames,2,aliases,2,&result))return 8;
    initialize();
    if(!rejected(QOTOM_ROOT_BUILD_PROTECTED,&source,&closed,&copy,
            protected_frames,0,aliases,2,&result))return 9;
    initialize();
    if(!rejected(QOTOM_ROOT_BUILD_ALIAS,&source,&closed,&copy,
            protected_frames,2,aliases,0,&result))return 10;
    initialize();
    if(!rejected(QOTOM_ROOT_BUILD_STORAGE,&source,&closed,&copy,
            protected_frames,2,aliases,2,
            (struct qotom_root_build_result *)&source.pt[300]))return 11;
    initialize();closed.pml4[0]=3;closed.pml4[1]=4;
    if(!rejected(QOTOM_ROOT_BUILD_STORAGE,&source,&closed,&copy,
            closed.pml4,2,aliases,2,&result))return 12;
    printf("Qotom copy-root builder: %u cases PASS\n",cases);
    return 0;
}
