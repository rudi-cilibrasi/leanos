#ifndef LEANOS_QOTOM_COPY_ROOT_BUILDER_H
#define LEANOS_QOTOM_COPY_ROOT_BUILDER_H

#include <stddef.h>
#include <stdint.h>

#define QOTOM_ROOT_LEAVES 4096u
#define QOTOM_ROOT_PT_PAGES 8u
#define QOTOM_ROOT_MAX_PROTECTED 16u
#define QOTOM_ROOT_MAX_ALIASES 2u
#define QOTOM_ROOT_ADDRESS_MASK UINT64_C(0x000ffffffffff000)
#define QOTOM_ROOT_PRESENT UINT64_C(1)
#define QOTOM_ROOT_WRITABLE UINT64_C(2)
#define QOTOM_ROOT_USER UINT64_C(4)
#define QOTOM_ROOT_ACCESSED UINT64_C(0x20)
#define QOTOM_ROOT_DIRTY UINT64_C(0x40)
#define QOTOM_ROOT_NX (UINT64_C(1) << 63)

/* One complete four-level root for the existing 16 MiB, 4 KiB-leaf domain.
 * Every array is a whole page and the type itself has page alignment. */
struct qotom_root_pages {
    _Alignas(4096) uint64_t pml4[512];
    uint64_t pdpt[512];
    uint64_t pd[512];
    uint64_t pt[QOTOM_ROOT_LEAVES];
};

struct qotom_copy_alias {
    uint64_t page;
    uint64_t frame;
    uint64_t writable;
};

struct qotom_root_build_result {
    uint64_t protected_count;
    uint64_t removed_aliases;
    uint64_t retained_present;
    uint64_t alias_count;
};

enum qotom_root_build_status {
    QOTOM_ROOT_BUILD_OK,
    QOTOM_ROOT_BUILD_STORAGE,
    QOTOM_ROOT_BUILD_SOURCE,
    QOTOM_ROOT_BUILD_PROTECTED,
    QOTOM_ROOT_BUILD_ALIAS
};

_Static_assert(sizeof(struct qotom_root_pages) == 11u * 4096u,
               "Qotom root storage must contain exactly eleven pages");
_Static_assert(_Alignof(struct qotom_root_pages) == 4096u,
               "Qotom root storage must be page aligned");

static inline int qotom_root_ranges_disjoint(
        const void *left, size_t left_bytes,
        const void *right, size_t right_bytes) {
    uintptr_t a=(uintptr_t)left, b=(uintptr_t)right;
    return left_bytes==0 || right_bytes==0 ||
        (a<=b ? b-a>=left_bytes : a-b>=right_bytes);
}

static inline int qotom_root_protected_frame(
        uint64_t frame, const uint64_t *protected_frames,
        size_t protected_count) {
    for(size_t i=0;i<protected_count;++i)
        if(protected_frames[i]==frame)return 1;
    return 0;
}

static inline int qotom_root_source_ancestors(
        const struct qotom_root_pages *source) {
    const uint64_t pml4_expected=(uintptr_t)source->pdpt|7u;
    const uint64_t pdpt_expected=(uintptr_t)source->pd|7u;
    if((source->pml4[0]&~QOTOM_ROOT_ACCESSED)!=pml4_expected ||
       (source->pdpt[0]&~QOTOM_ROOT_ACCESSED)!=pdpt_expected)return 0;
    for(size_t i=1;i<512;++i)
        if(source->pml4[i]!=0 || source->pdpt[i]!=0)return 0;
    for(size_t i=0;i<512;++i) {
        uint64_t expected=i<QOTOM_ROOT_PT_PAGES
            ? (uintptr_t)&source->pt[i*512u]|7u : 0;
        if((source->pd[i]&~QOTOM_ROOT_ACCESSED)!=expected)return 0;
    }
    return 1;
}

/* Construct two unpublished roots from one already generated and decoded
 * source root. The closed root removes every present alias of every supplied
 * physical frame. The copy root differs only at up to two source-absent slots,
 * where it installs supervisor/NX aliases of protected frames. Rejection
 * occurs before either output or the result record is written.
 *
 * This function cannot establish inventory completeness, storage ownership,
 * CR3 publication, TLB invalidation, or transfer-operand authority. Its native
 * caller must establish those obligations before publishing either root. */
static inline enum qotom_root_build_status qotom_build_copy_roots(
        const struct qotom_root_pages *source,
        struct qotom_root_pages *closed,
        struct qotom_root_pages *copy,
        const uint64_t *protected_frames, size_t protected_count,
        const struct qotom_copy_alias *aliases, size_t alias_count,
        struct qotom_root_build_result *result) {
    const size_t root_bytes=sizeof(*closed);
    if(!source || !closed || !copy || !protected_frames || !aliases || !result ||
       ((uintptr_t)source&4095u) || ((uintptr_t)closed&4095u) ||
       ((uintptr_t)copy&4095u) ||
       !qotom_root_ranges_disjoint(source,root_bytes,closed,root_bytes) ||
       !qotom_root_ranges_disjoint(source,root_bytes,copy,root_bytes) ||
       !qotom_root_ranges_disjoint(closed,root_bytes,copy,root_bytes) ||
       !qotom_root_ranges_disjoint(source,root_bytes,result,sizeof(*result)) ||
       !qotom_root_ranges_disjoint(closed,root_bytes,result,sizeof(*result)) ||
       !qotom_root_ranges_disjoint(copy,root_bytes,result,sizeof(*result)))
        return QOTOM_ROOT_BUILD_STORAGE;
    if(!qotom_root_source_ancestors(source))return QOTOM_ROOT_BUILD_SOURCE;
    if(protected_count==0 || protected_count>QOTOM_ROOT_MAX_PROTECTED)
        return QOTOM_ROOT_BUILD_PROTECTED;
    for(size_t i=0;i<protected_count;++i) {
        if(protected_frames[i]>=(UINT64_C(1)<<40))
            return QOTOM_ROOT_BUILD_PROTECTED;
        for(size_t j=0;j<i;++j)
            if(protected_frames[i]==protected_frames[j])
                return QOTOM_ROOT_BUILD_PROTECTED;
    }
    if(alias_count==0 || alias_count>QOTOM_ROOT_MAX_ALIASES)
        return QOTOM_ROOT_BUILD_ALIAS;
    if(!qotom_root_ranges_disjoint(closed,root_bytes,protected_frames,
            protected_count*sizeof(*protected_frames)) ||
       !qotom_root_ranges_disjoint(copy,root_bytes,protected_frames,
            protected_count*sizeof(*protected_frames)) ||
       !qotom_root_ranges_disjoint(result,sizeof(*result),protected_frames,
            protected_count*sizeof(*protected_frames)) ||
       !qotom_root_ranges_disjoint(closed,root_bytes,aliases,
            alias_count*sizeof(*aliases)) ||
       !qotom_root_ranges_disjoint(copy,root_bytes,aliases,
            alias_count*sizeof(*aliases)) ||
       !qotom_root_ranges_disjoint(result,sizeof(*result),aliases,
            alias_count*sizeof(*aliases)))
        return QOTOM_ROOT_BUILD_STORAGE;
    for(size_t i=0;i<alias_count;++i) {
        if(aliases[i].page>=QOTOM_ROOT_LEAVES || aliases[i].writable>1 ||
           source->pt[aliases[i].page]!=0 ||
           !qotom_root_protected_frame(
               aliases[i].frame,protected_frames,protected_count))
            return QOTOM_ROOT_BUILD_ALIAS;
        for(size_t j=0;j<i;++j)
            if(aliases[i].page==aliases[j].page ||
               aliases[i].frame==aliases[j].frame)
                return QOTOM_ROOT_BUILD_ALIAS;
    }

    for(size_t i=0;i<512;++i) {
        closed->pml4[i]=0;closed->pdpt[i]=0;closed->pd[i]=0;
        copy->pml4[i]=0;copy->pdpt[i]=0;copy->pd[i]=0;
    }
    closed->pml4[0]=(uintptr_t)closed->pdpt|7u;
    closed->pdpt[0]=(uintptr_t)closed->pd|7u;
    copy->pml4[0]=(uintptr_t)copy->pdpt|7u;
    copy->pdpt[0]=(uintptr_t)copy->pd|7u;
    for(size_t i=0;i<QOTOM_ROOT_PT_PAGES;++i) {
        closed->pd[i]=(uintptr_t)&closed->pt[i*512u]|7u;
        copy->pd[i]=(uintptr_t)&copy->pt[i*512u]|7u;
    }
    uint64_t removed=0,retained=0;
    for(size_t page=0;page<QOTOM_ROOT_LEAVES;++page) {
        uint64_t leaf=source->pt[page];
        int remove=(leaf&QOTOM_ROOT_PRESENT) && qotom_root_protected_frame(
            (leaf&QOTOM_ROOT_ADDRESS_MASK)>>12,
            protected_frames,protected_count);
        closed->pt[page]=remove?0:leaf;
        copy->pt[page]=remove?0:leaf;
        if(remove)++removed;
        else if(leaf&QOTOM_ROOT_PRESENT)++retained;
    }
    for(size_t i=0;i<alias_count;++i)
        copy->pt[aliases[i].page]=(aliases[i].frame<<12)|
            QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX|
            (aliases[i].writable?QOTOM_ROOT_WRITABLE:0);
    *result=(struct qotom_root_build_result){
        protected_count,removed,retained,alias_count};
    return QOTOM_ROOT_BUILD_OK;
}

#endif
