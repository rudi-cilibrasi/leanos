#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "frame_copy_window.h"

static struct qotom_root_pages source,closed,copy,fetch,send;
static struct qotom_root_build_result result;
static const uint64_t protected_frames[2]={3,4};
static const struct qotom_copy_alias aliases[2]={{100,3,0},{101,4,1}};
static unsigned cases;
/* Where each root's tables are, as its entries and CR3 name them: the
 * storage's own address (the identity-mapped kernel), or placements that
 * differ from it, which only the integers carry (issue #599). */
static uint64_t source_phys,closed_phys,copy_phys;

static void place(int identity) {
    source_phys=identity?qotom_root_phys(&source):UINT64_C(0x200000);
    closed_phys=identity?qotom_root_phys(&closed):UINT64_C(0x20b000);
    copy_phys=identity?qotom_root_phys(&copy):UINT64_C(0x7ffffff4000);
}

static void initialize(void) {
    memset(&source,0,sizeof(source));
    source.pml4[0]=qotom_root_table_entry(source_phys,1);
    source.pdpt[0]=qotom_root_table_entry(source_phys,2)|QOTOM_ROOT_ACCESSED;
    for(unsigned i=0;i<QOTOM_ROOT_PT_PAGES;++i)
        source.pd[i]=qotom_root_table_entry(source_phys,3+i);
    for(unsigned i=0;i<QOTOM_ROOT_LEAVES;++i)
        source.pt[i]=(uint64_t)i<<12|QOTOM_ROOT_PRESENT|
            QOTOM_ROOT_WRITABLE|QOTOM_ROOT_NX;
    source.pt[100]=source.pt[101]=0;
    source.pt[200]=(UINT64_C(3)<<12)|QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX;
    source.pt[201]=(UINT64_C(4)<<12)|QOTOM_ROOT_PRESENT|
        QOTOM_ROOT_WRITABLE|QOTOM_ROOT_USER|QOTOM_ROOT_NX;
    source.pt[202]=(UINT64_C(3)<<12)|QOTOM_ROOT_DIRTY;  /* absent: kept */
    memset(&closed,0xa5,sizeof(closed));memset(&copy,0x5a,sizeof(copy));
    memset(&result,0x3c,sizeof(result));
}

static int built(const uint64_t *frames) {
    if(qotom_build_copy_roots(&source,source_phys,&closed,closed_phys,
            &copy,copy_phys,frames,2,aliases,2,&result)!=QOTOM_ROOT_BUILD_OK)
        return 0;
    if(result.protected_count!=2 || result.removed_aliases!=4 ||
       result.retained_present!=4089 || result.alias_count!=2)return 0;
    if(!qotom_root_source_ancestors(&closed,closed_phys) ||
       !qotom_root_source_ancestors(&copy,copy_phys) ||
       closed.pml4[0]!=((closed_phys+4096u)|7u) ||
       copy.pd[7]!=((copy_phys+10u*4096u)|7u))return 0;
    for(unsigned page=0;page<QOTOM_ROOT_LEAVES;++page) {
        uint64_t s=source.pt[page],a=closed.pt[page],b=copy.pt[page];
        int removed=(s&QOTOM_ROOT_PRESENT) &&
            ((s&QOTOM_ROOT_ADDRESS_MASK)==(UINT64_C(3)<<12) ||
             (s&QOTOM_ROOT_ADDRESS_MASK)==(UINT64_C(4)<<12));
        if(a!=(removed?0:s))return 0;
        if(page!=100 && page!=101 && a!=b)return 0;
    }
    return copy.pt[100]==((UINT64_C(3)<<12)|QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX) &&
           copy.pt[101]==((UINT64_C(4)<<12)|QOTOM_ROOT_PRESENT|
                          QOTOM_ROOT_WRITABLE|QOTOM_ROOT_NX);
}

static int accepted(int identity) {
    ++cases;place(identity);initialize();
    return built(protected_frames);
}

static int rejected(enum qotom_root_build_status expected,
        const struct qotom_root_pages *s,uint64_t sp,struct qotom_root_pages *a,
        uint64_t ap,struct qotom_root_pages *b,uint64_t bp,
        const uint64_t *frames,size_t frame_count,
        const struct qotom_copy_alias *map,size_t map_count,
        struct qotom_root_build_result *record) {
    ++cases;
    static unsigned char before_source[sizeof(source)];
    static unsigned char before_closed[sizeof(closed)],before_copy[sizeof(copy)];
    struct qotom_root_build_result before_result=result;
    memcpy(before_source,&source,sizeof(source));
    memcpy(before_closed,&closed,sizeof(closed));memcpy(before_copy,&copy,sizeof(copy));
    enum qotom_root_build_status got=qotom_build_copy_roots(
        s,sp,a,ap,b,bp,frames,frame_count,map,map_count,record);
    return got==expected && !memcmp(before_source,&source,sizeof(source)) &&
        !memcmp(before_closed,&closed,sizeof(closed)) &&
        !memcmp(before_copy,&copy,sizeof(copy)) &&
        !memcmp(&before_result,&result,sizeof(result));
}

/* frame_window_build over the same source: a two-page window of frames 3
 * and 4 aliased at pages 100 and 101, which the source leaves absent. */
static int window_cases(void) {
    place(0);initialize();
    struct frame_window w={&fetch,&send,UINT64_C(0x300000),UINT64_C(0x30b000),
        UINT64_C(3)<<12,UINT64_C(5)<<12,100};
    struct qotom_root_build_result first;
    int built=0;
    ++cases;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_OK || !built ||
       first.protected_count!=2 || first.removed_aliases!=4 ||
       first.retained_present!=4089 || first.alias_count!=2)return 0;
    if(!frame_window_root_exact(&fetch,w.fetch_phys,&closed,closed_phys,
            protected_frames,2,&w,1) ||
       !frame_window_root_exact(&send,w.send_phys,&closed,closed_phys,
            protected_frames,2,&w,0) ||
       !qotom_root_source_ancestors(&fetch,w.fetch_phys) ||
       fetch.pt[101]!=((UINT64_C(4)<<12)|QOTOM_ROOT_PRESENT|QOTOM_ROOT_WRITABLE|QOTOM_ROOT_NX) ||
       send.pt[101]!=((UINT64_C(4)<<12)|QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX) ||
       fetch.pt[3]!=0 || send.pt[7]!=source.pt[7])return 0;
    /* The scan rejects a changed leaf, the other root's permission, and a
     * closed root that maps a protected frame, even where both agree. */
    ++cases;fetch.pt[7]^=QOTOM_ROOT_USER;
    if(frame_window_root_exact(&fetch,w.fetch_phys,&closed,closed_phys,
            protected_frames,2,&w,1))return 0;
    fetch.pt[7]^=QOTOM_ROOT_USER;
    ++cases;
    if(frame_window_root_exact(&send,w.send_phys,&closed,closed_phys,
            protected_frames,2,&w,1))return 0;
    ++cases;closed.pt[300]=fetch.pt[300]=(UINT64_C(3)<<12)|QOTOM_ROOT_PRESENT;
    if(frame_window_root_exact(&fetch,w.fetch_phys,&closed,closed_phys,
            protected_frames,2,&w,1))return 0;
    ++cases;
    if(frame_window_root_exact(&fetch,w.fetch_phys+4096u,&closed,closed_phys,
            protected_frames,2,&w,1))return 0;
    /* A rebuild must reproduce the first build's counts. */
    ++cases;first.removed_aliases=3;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_REBUILD)return 0;
    first.removed_aliases=4;
    ++cases;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_OK)return 0;
    /* The window roots must not overlap each other. */
    ++cases;w.send_phys=w.fetch_phys;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_BUILD)return 0;
    ++cases;w.send_phys=w.fetch_phys+4096u;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_BUILD)return 0;
    w.send_phys=UINT64_C(0x30b000);
    /* The geometry, an occupied alias slot and a window frame outside the
     * inventory. */
    ++cases;w.base+=8u;w.limit+=8u;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_GEOMETRY)return 0;
    w.base-=8u;w.limit-=8u;
    ++cases;w.slot=101;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_BUILD)return 0;
    w.slot=100;
    ++cases;w.base=UINT64_C(4)<<12;w.limit=UINT64_C(6)<<12;
    if(frame_window_build(&source,source_phys,&closed,closed_phys,protected_frames,2,
            &w,&first,&built)!=FRAME_WINDOW_BUILD)return 0;
    return 1;
}

#define REJECT(code,status,sp,ap,bp,frames,n,map,m) do { \
        if(!rejected(status,&source,sp,&closed,ap,&copy,bp,frames,n,map,m, \
                &result))return code; } while(0)

int main(void) {
#ifndef __COMPCERT__
    /* The identity placement converts the storage's address to an integer,
     * which CompCert's memory model leaves undefined: its interpreter
     * (scripts/check-compcert-interp.sh) runs every other case. */
    if(!accepted(1))return 1;
#endif
    if(!accepted(0))return 2;
    const uint64_t root_bytes=sizeof(struct qotom_root_pages);
    place(0);
    initialize();source.pml4[0]^=4096;
    REJECT(3,QOTOM_ROOT_BUILD_SOURCE,source_phys,closed_phys,copy_phys,
        protected_frames,2,aliases,2);
    initialize();source.pd[0]|=UINT64_C(0x80);
    REJECT(4,QOTOM_ROOT_BUILD_SOURCE,source_phys,closed_phys,copy_phys,
        protected_frames,2,aliases,2);
    initialize();
    REJECT(5,QOTOM_ROOT_BUILD_SOURCE,source_phys-4096u,closed_phys,copy_phys,
        protected_frames,2,aliases,2);
    initialize();source.pd[8]=qotom_root_table_entry(source_phys,11);
    REJECT(6,QOTOM_ROOT_BUILD_SOURCE,source_phys,closed_phys,copy_phys,
        protected_frames,2,aliases,2);
    initialize();uint64_t duplicate[2]={3,3};
    REJECT(7,QOTOM_ROOT_BUILD_PROTECTED,source_phys,closed_phys,copy_phys,
        duplicate,2,aliases,2);
    initialize();uint64_t wide[2]={3,UINT64_C(1)<<40};
    REJECT(8,QOTOM_ROOT_BUILD_PROTECTED,source_phys,closed_phys,copy_phys,
        wide,2,aliases,2);
    initialize();
    REJECT(9,QOTOM_ROOT_BUILD_PROTECTED,source_phys,closed_phys,copy_phys,
        protected_frames,0,aliases,2);
    initialize();
    REJECT(10,QOTOM_ROOT_BUILD_PROTECTED,source_phys,closed_phys,copy_phys,
        protected_frames,QOTOM_ROOT_MAX_PROTECTED+1u,aliases,2);
    initialize();struct qotom_copy_alias occupied[2]={{99,3,0},{101,4,0}};
    REJECT(11,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,occupied,2);
    initialize();struct qotom_copy_alias foreign[2]={{100,3,0},{101,5,0}};
    REJECT(12,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,foreign,2);
    initialize();struct qotom_copy_alias same_slot[2]={{100,3,0},{100,4,0}};
    REJECT(13,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,same_slot,2);
    initialize();struct qotom_copy_alias same_frame[2]={{100,3,0},{101,3,0}};
    REJECT(14,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,same_frame,2);
    initialize();struct qotom_copy_alias outside[2]={{100,3,0},{4096,4,0}};
    REJECT(15,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,outside,2);
    initialize();struct qotom_copy_alias permission[2]={{100,3,2},{101,4,0}};
    REJECT(16,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,permission,2);
    initialize();
    REJECT(17,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,aliases,0);
    initialize();
    REJECT(18,QOTOM_ROOT_BUILD_ALIAS,source_phys,closed_phys,copy_phys,
        protected_frames,2,aliases,QOTOM_ROOT_MAX_ALIASES+1u);
    /* Physical storage: aligned, nonzero, representable, disjoint. */
    initialize();
    REJECT(19,QOTOM_ROOT_BUILD_STORAGE,source_phys,closed_phys,closed_phys,
        protected_frames,2,aliases,2);
    initialize();
    REJECT(20,QOTOM_ROOT_BUILD_STORAGE,source_phys,closed_phys,
        closed_phys+root_bytes-4096u,protected_frames,2,aliases,2);
    initialize();
    REJECT(21,QOTOM_ROOT_BUILD_STORAGE,source_phys,source_phys+4096u,copy_phys,
        protected_frames,2,aliases,2);
    initialize();
    REJECT(22,QOTOM_ROOT_BUILD_STORAGE,source_phys,closed_phys+8u,copy_phys,
        protected_frames,2,aliases,2);
    initialize();
    REJECT(23,QOTOM_ROOT_BUILD_STORAGE,source_phys,0,copy_phys,
        protected_frames,2,aliases,2);
    initialize();
    REJECT(24,QOTOM_ROOT_BUILD_STORAGE,source_phys,closed_phys,
        QOTOM_ROOT_PHYS_LIMIT-root_bytes+4096u,protected_frames,2,aliases,2);
    initialize();
    if(!rejected(QOTOM_ROOT_BUILD_STORAGE,&source,source_phys,&closed,closed_phys,
            &copy,copy_phys,protected_frames,2,aliases,2,0))return 25;
    /* Adjacent storage is disjoint, and the highest representable
     * placement is accepted. */
    ++cases;initialize();copy_phys=closed_phys+root_bytes;
    if(!built(protected_frames))return 26;
    ++cases;initialize();copy_phys=QOTOM_ROOT_PHYS_LIMIT-root_bytes;
    if(!built(protected_frames))return 27;
    /* The builder copies the inventory before writing an output, so an
     * inventory stored in the closed root's own storage still yields the
     * same roots. */
    ++cases;place(0);initialize();closed.pml4[0]=3;closed.pml4[1]=4;
    if(!built(closed.pml4))return 28;
    if(!window_cases())return 29;
    printf("Qotom copy-root builder: %u cases PASS\n",cases);
    return 0;
}
