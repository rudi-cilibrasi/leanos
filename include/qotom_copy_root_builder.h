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

#define QOTOM_ROOT_TABLE_FLAGS UINT64_C(7)
#define QOTOM_ROOT_PHYS_LIMIT (UINT64_C(1) << 52)

_Static_assert(sizeof(struct qotom_root_pages) == 11u * 4096u,
               "Qotom root storage must contain exactly eleven pages");
_Static_assert(_Alignof(struct qotom_root_pages) == 4096u,
               "Qotom root storage must be page aligned");

/* Every function below takes a root's physical address as an integer, the
 * address its own entries and CR3 name, and computes every table entry from
 * it. The kernel and the lab images identity-map their storage, so their
 * physical address is the storage's address: native callers obtain it only
 * through this helper, which holds that assumption (issue #599). */
static inline uint64_t qotom_root_phys(const struct qotom_root_pages *root) {
    return (uint64_t)(uintptr_t)root;
}

/* The non-leaf entry naming page `table` of the root at `root_phys`: 1 is
 * the PDPT, 2 the page directory, and 3 + i the i-th page table. */
static inline uint64_t qotom_root_table_entry(uint64_t root_phys, uint64_t table) {
    return (root_phys + table * 4096u) | QOTOM_ROOT_TABLE_FLAGS;
}

/* Root storage at `root_phys` can hold this root's page tables: nonzero,
 * page aligned, and every table address fits an entry's address field. */
static inline int qotom_root_phys_ok(uint64_t root_phys) {
    return root_phys != 0 && (root_phys & 4095u) == 0 &&
        root_phys <= QOTOM_ROOT_PHYS_LIMIT - sizeof(struct qotom_root_pages);
}

/* Two roots' storage does not overlap in physical memory. */
static inline int qotom_root_phys_disjoint(uint64_t left, uint64_t right) {
    const uint64_t bytes = sizeof(struct qotom_root_pages);
    return left <= right ? right - left >= bytes : left - right >= bytes;
}

static inline int qotom_root_protected_frame(
        uint64_t frame, const uint64_t *protected_frames,
        size_t protected_count) {
    for(size_t i=0;i<protected_count;++i)
        if(protected_frames[i]==frame)return 1;
    return 0;
}

/* `root` has the source hierarchy's shape at `root_phys`: one PML4 entry
 * naming its PDPT, one PDPT entry naming its page directory, and exactly
 * QOTOM_ROOT_PT_PAGES directory entries naming its page tables in order,
 * each with flags 7 (Accessed ignored), and no other non-leaf entry. */
static inline int qotom_root_source_ancestors(
        const struct qotom_root_pages *root, uint64_t root_phys) {
    if((root->pml4[0]&~QOTOM_ROOT_ACCESSED)!=qotom_root_table_entry(root_phys,1) ||
       (root->pdpt[0]&~QOTOM_ROOT_ACCESSED)!=qotom_root_table_entry(root_phys,2))
        return 0;
    for(size_t i=1;i<512;++i)
        if(root->pml4[i]!=0 || root->pdpt[i]!=0)return 0;
    for(size_t i=0;i<512;++i) {
        uint64_t expected=i<QOTOM_ROOT_PT_PAGES
            ? qotom_root_table_entry(root_phys,3+i) : 0;
        if((root->pd[i]&~QOTOM_ROOT_ACCESSED)!=expected)return 0;
    }
    return 1;
}

/* Construct two unpublished roots from one already generated and decoded
 * source root. The closed root removes every present alias of every supplied
 * physical frame. The copy root differs only at up to two source-absent slots,
 * where it installs supervisor/NX aliases of protected frames. Rejection
 * occurs before either output or the result record is written.
 *
 * Each root is named by its storage and its physical address. The three
 * physical ranges must be disjoint, page aligned and representable; the
 * caller must pass the address its storage really has (qotom_root_phys on
 * the identity-mapped kernel). The protected frames and aliases are copied
 * before any output is written, so they may live anywhere; the result record
 * must not overlap a root.
 *
 * This function cannot establish inventory completeness, storage ownership,
 * CR3 publication, TLB invalidation, or transfer-operand authority. Its native
 * caller must establish those obligations before publishing either root. */
static inline enum qotom_root_build_status qotom_build_copy_roots(
        const struct qotom_root_pages *source, uint64_t source_phys,
        struct qotom_root_pages *closed, uint64_t closed_phys,
        struct qotom_root_pages *copy, uint64_t copy_phys,
        const uint64_t *protected_frames, size_t protected_count,
        const struct qotom_copy_alias *aliases, size_t alias_count,
        struct qotom_root_build_result *result) {
    uint64_t frames[QOTOM_ROOT_MAX_PROTECTED];
    uint64_t alias_page[QOTOM_ROOT_MAX_ALIASES];
    uint64_t alias_frame[QOTOM_ROOT_MAX_ALIASES];
    uint64_t alias_writable[QOTOM_ROOT_MAX_ALIASES];
    if(!source || !closed || !copy || !protected_frames || !aliases || !result ||
       !qotom_root_phys_ok(source_phys) || !qotom_root_phys_ok(closed_phys) ||
       !qotom_root_phys_ok(copy_phys) ||
       !qotom_root_phys_disjoint(source_phys,closed_phys) ||
       !qotom_root_phys_disjoint(source_phys,copy_phys) ||
       !qotom_root_phys_disjoint(closed_phys,copy_phys))
        return QOTOM_ROOT_BUILD_STORAGE;
    if(!qotom_root_source_ancestors(source,source_phys))
        return QOTOM_ROOT_BUILD_SOURCE;
    if(protected_count==0 || protected_count>QOTOM_ROOT_MAX_PROTECTED)
        return QOTOM_ROOT_BUILD_PROTECTED;
    for(size_t i=0;i<protected_count;++i) {
        uint64_t frame=protected_frames[i];
        if(frame>=(UINT64_C(1)<<40))return QOTOM_ROOT_BUILD_PROTECTED;
        for(size_t j=0;j<i;++j)
            if(frame==frames[j])return QOTOM_ROOT_BUILD_PROTECTED;
        frames[i]=frame;
    }
    if(alias_count==0 || alias_count>QOTOM_ROOT_MAX_ALIASES)
        return QOTOM_ROOT_BUILD_ALIAS;
    for(size_t i=0;i<alias_count;++i) {
        uint64_t page=aliases[i].page;
        uint64_t frame=aliases[i].frame;
        uint64_t writable=aliases[i].writable;
        if(page>=QOTOM_ROOT_LEAVES || writable>1 || source->pt[page]!=0 ||
           !qotom_root_protected_frame(frame,frames,protected_count))
            return QOTOM_ROOT_BUILD_ALIAS;
        for(size_t j=0;j<i;++j)
            if(page==alias_page[j] || frame==alias_frame[j])
                return QOTOM_ROOT_BUILD_ALIAS;
        alias_page[i]=page;
        alias_frame[i]=frame;
        alias_writable[i]=writable;
    }

    for(size_t i=0;i<512;++i) {
        closed->pml4[i]=0;closed->pdpt[i]=0;closed->pd[i]=0;
        copy->pml4[i]=0;copy->pdpt[i]=0;copy->pd[i]=0;
    }
    closed->pml4[0]=qotom_root_table_entry(closed_phys,1);
    closed->pdpt[0]=qotom_root_table_entry(closed_phys,2);
    copy->pml4[0]=qotom_root_table_entry(copy_phys,1);
    copy->pdpt[0]=qotom_root_table_entry(copy_phys,2);
    for(size_t i=0;i<QOTOM_ROOT_PT_PAGES;++i) {
        closed->pd[i]=qotom_root_table_entry(closed_phys,3+i);
        copy->pd[i]=qotom_root_table_entry(copy_phys,3+i);
    }
    uint64_t removed=0,retained=0;
    for(size_t page=0;page<QOTOM_ROOT_LEAVES;++page) {
        uint64_t leaf=source->pt[page];
        int remove=(leaf&QOTOM_ROOT_PRESENT) && qotom_root_protected_frame(
            (leaf&QOTOM_ROOT_ADDRESS_MASK)>>12,frames,protected_count);
        closed->pt[page]=remove?0:leaf;
        copy->pt[page]=remove?0:leaf;
        if(remove)++removed;
        else if(leaf&QOTOM_ROOT_PRESENT)++retained;
    }
    for(size_t i=0;i<alias_count;++i)
        copy->pt[alias_page[i]]=(alias_frame[i]<<12)|
            QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX|
            (alias_writable[i]?QOTOM_ROOT_WRITABLE:0);
    result->protected_count=protected_count;
    result->removed_aliases=removed;
    result->retained_present=retained;
    result->alias_count=alias_count;
    return QOTOM_ROOT_BUILD_OK;
}

#endif
