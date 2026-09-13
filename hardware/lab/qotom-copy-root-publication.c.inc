#include "../../include/qotom_copy_root_builder.h"

struct qotom_copy_operand { uint64_t source, destination; };
extern uint64_t leanos_copy_root_transfer(
    uint64_t closed_root, uint64_t copy_root,
    const struct qotom_copy_operand *operands, uint64_t count);
#ifdef LEANOS_QOTOM_ENTRY_INTEGRATION
static __attribute__((noreturn,noinline)) void lab_run_qotom_entry_integration(void);
#endif

static struct qotom_root_pages qotom_closed_root;
static struct qotom_root_pages qotom_copy_root;
static struct qotom_root_build_result qotom_root_result;
static uint64_t qotom_protected_frames[QOTOM_ROOT_MAX_PROTECTED];
static struct qotom_copy_alias qotom_aliases[QOTOM_ROOT_MAX_ALIASES];
static struct qotom_copy_operand qotom_operands[16];
static uint8_t qotom_copy_destination[16];

static void qotom_add_protected_range(
        uintptr_t first, uintptr_t past, size_t *count) {
    if(first>=past || (first&4095u))pre_admission_fail("qotom-root-inventory-range");
    uintptr_t rounded=(past+4095u)&~(uintptr_t)4095u;
    if(rounded<past)pre_admission_fail("qotom-root-inventory-overflow");
    for(uintptr_t address=first;address<rounded;address+=4096u) {
        uint64_t frame=address>>12;
        for(size_t i=0;i<*count;++i)
            if(qotom_protected_frames[i]==frame)
                pre_admission_fail("qotom-root-inventory-duplicate");
        if(*count>=QOTOM_ROOT_MAX_PROTECTED)
            pre_admission_fail("qotom-root-inventory-bounds");
        qotom_protected_frames[(*count)++]=frame;
    }
}

static int qotom_root_storage_mapped(
        const struct qotom_root_pages *source,
        const struct qotom_root_pages *storage) {
    uintptr_t first=(uintptr_t)storage;
    uintptr_t past=first+sizeof(*storage);
    if(first==0 || (first&4095u) || past<first || past>UINT64_C(0x1000000))
        return 0;
    for(uintptr_t address=first;address<past;address+=4096u) {
        uint64_t page=address>>12;
        uint64_t expected=(address&~(uintptr_t)4095u)|QOTOM_ROOT_PRESENT|
            QOTOM_ROOT_WRITABLE|QOTOM_ROOT_NX;
        if(page>=QOTOM_ROOT_LEAVES ||
           (source->pt[page]&~(QOTOM_ROOT_ACCESSED|QOTOM_ROOT_DIRTY))!=expected)
            return 0;
    }
    return 1;
}

static int qotom_closed_root_exact(size_t protected_count) {
    if(!qotom_root_source_ancestors(&qotom_closed_root))return 0;
    for(size_t page=0;page<QOTOM_ROOT_LEAVES;++page) {
        uint64_t leaf=qotom_closed_root.pt[page];
        if((leaf&QOTOM_ROOT_PRESENT) && qotom_root_protected_frame(
                (leaf&QOTOM_ROOT_ADDRESS_MASK)>>12,
                qotom_protected_frames,protected_count))return 0;
    }
    return 1;
}

static int qotom_copy_root_exact(size_t protected_count) {
    if(!qotom_root_source_ancestors(&qotom_copy_root))return 0;
    for(size_t page=0;page<QOTOM_ROOT_LEAVES;++page) {
        uint64_t leaf=qotom_copy_root.pt[page];
        int alias=-1;
        for(size_t i=0;i<QOTOM_ROOT_MAX_ALIASES;++i)
            if(qotom_aliases[i].page==page)alias=(int)i;
        if(alias>=0) {
            uint64_t expected=(qotom_aliases[alias].frame<<12)|
                QOTOM_ROOT_PRESENT|QOTOM_ROOT_NX;
            /* A completed transfer may set hardware-maintained Accessed/Dirty
             * metadata without changing the alias identity or permissions. */
            if((leaf&~(QOTOM_ROOT_ACCESSED|QOTOM_ROOT_DIRTY))!=expected)return 0;
        } else if((leaf&QOTOM_ROOT_PRESENT) && qotom_root_protected_frame(
                (leaf&QOTOM_ROOT_ADDRESS_MASK)>>12,
                qotom_protected_frames,protected_count))return 0;
    }
    return 1;
}

static __attribute__((noreturn,noinline)) void lab_publish_qotom_copy_roots(void) {
    const struct qotom_root_pages *source=
        (const struct qotom_root_pages *)page_map_level_4_a;
    if((const uint64_t *)source->pdpt!=page_directory_pointer_a ||
       (const uint64_t *)source->pd!=page_directory_a ||
       (const uint64_t *)source->pt!=page_table_a ||
       !qotom_root_source_ancestors(source))
        pre_admission_fail("qotom-root-source");
    size_t protected_count=0;
    qotom_add_protected_range((uintptr_t)__user_a_text_start,
        (uintptr_t)__user_a_text_end,&protected_count);
    qotom_add_protected_range((uintptr_t)__user_a_stack_start,
        (uintptr_t)__user_a_stack_end,&protected_count);
    qotom_add_protected_range((uintptr_t)__user_b_text_start,
        (uintptr_t)__user_b_text_end,&protected_count);
    qotom_add_protected_range((uintptr_t)__user_b_stack_start,
        (uintptr_t)__user_b_stack_end,&protected_count);
    if(protected_count!=5 ||
       (uintptr_t)__user_a_stack_end-(uintptr_t)__user_a_stack_start!=8192u)
        pre_admission_fail("qotom-root-inventory-count");
    if(!qotom_root_storage_mapped(source,&qotom_closed_root) ||
       !qotom_root_storage_mapped(source,&qotom_copy_root))
        pre_admission_fail("qotom-root-storage");

    qotom_aliases[0]=(struct qotom_copy_alias){
        (uintptr_t)__user_b_text_start>>12,
        (uintptr_t)__user_a_stack_start>>12,0};
    qotom_aliases[1]=(struct qotom_copy_alias){
        (uintptr_t)__user_b_stack_start>>12,
        ((uintptr_t)__user_a_stack_start>>12)+1u,0};
    enum qotom_root_build_status build=qotom_build_copy_roots(source,
        &qotom_closed_root,&qotom_copy_root,qotom_protected_frames,
        protected_count,qotom_aliases,QOTOM_ROOT_MAX_ALIASES,
        &qotom_root_result);
    int closed_scan=qotom_closed_root_exact(protected_count);
    int copy_scan=qotom_copy_root_exact(protected_count);

    volatile uint8_t *user=(volatile uint8_t *)__user_a_stack_start+4090u;
    for(size_t i=0;i<16;++i)user[i]=(uint8_t)(0xa0u+i);
    for(size_t i=0;i<16;++i) {
        uint64_t offset=4090u+i;
        uint64_t alias=i<6?qotom_aliases[0].page:qotom_aliases[1].page;
        qotom_operands[i]=(struct qotom_copy_operand){
            alias*4096u+(offset&4095u),(uintptr_t)&qotom_copy_destination[i]};
        qotom_copy_destination[i]=0;
    }
    uint64_t transferred=0;
    if(build==QOTOM_ROOT_BUILD_OK && closed_scan && copy_scan)
        transferred=leanos_copy_root_transfer(
            (uintptr_t)qotom_closed_root.pml4,
            (uintptr_t)qotom_copy_root.pml4,qotom_operands,16);
    uint64_t active_root;
    __asm__ volatile("mov %%cr3,%0":"=r"(active_root));
    active_root&=QOTOM_ROOT_ADDRESS_MASK;
    uint64_t bytes_match=1;
    for(size_t i=0;i<16;++i)
        if(qotom_copy_destination[i]!=(uint8_t)(0xa0u+i))bytes_match=0;
    uint64_t accepted=leanos_qotom_copy_root_publication_query(
        build,qotom_root_result.protected_count,qotom_root_result.removed_aliases,
        qotom_root_result.retained_present,qotom_root_result.alias_count,
        (uintptr_t)qotom_closed_root.pml4,(uintptr_t)qotom_copy_root.pml4,
        closed_scan,copy_scan,transferred,bytes_match,active_root,1);
    uint64_t errors=leanos_qotom_copy_root_publication_query(
        build,qotom_root_result.protected_count,qotom_root_result.removed_aliases,
        qotom_root_result.retained_present,qotom_root_result.alias_count,
        (uintptr_t)qotom_closed_root.pml4,(uintptr_t)qotom_copy_root.pml4,
        closed_scan,copy_scan,transferred,bytes_match,active_root,2);
    serial_puts("LEANOS-LAB/1 COPY-ROOTS profile=qotom-copy-roots-v1 status=");
    serial_u64(accepted==1?0:1);
    serial_puts(" protected=");serial_u64(qotom_root_result.protected_count);
    serial_puts(" removed-aliases=");serial_u64(qotom_root_result.removed_aliases);
    serial_puts(" retained-present=");serial_u64(qotom_root_result.retained_present);
    serial_puts(" aliases=");serial_u64(qotom_root_result.alias_count);
    serial_puts(" closed-root=");serial_u64((uintptr_t)qotom_closed_root.pml4);
    serial_puts(" copy-root=");serial_u64((uintptr_t)qotom_copy_root.pml4);
    serial_puts(" closed-scan=");serial_u64(closed_scan);
    serial_puts(" copy-scan=");serial_u64(copy_scan);
    serial_puts(" transferred=");serial_u64(transferred);
    serial_puts(" bytes-match=");serial_u64(bytes_match);
    serial_puts(" active-root=");serial_u64(active_root);
    serial_puts(" error-mask=");serial_u64(errors);
    serial_puts(" closed-root-published=");
    serial_u64(leanos_qotom_copy_root_publication_query(
        build,qotom_root_result.protected_count,qotom_root_result.removed_aliases,
        qotom_root_result.retained_present,qotom_root_result.alias_count,
        (uintptr_t)qotom_closed_root.pml4,(uintptr_t)qotom_copy_root.pml4,
        closed_scan,copy_scan,transferred,bytes_match,active_root,3));
    serial_puts(" copy-root-published=");
    serial_u64(leanos_qotom_copy_root_publication_query(
        build,qotom_root_result.protected_count,qotom_root_result.removed_aliases,
        qotom_root_result.retained_present,qotom_root_result.alias_count,
        (uintptr_t)qotom_closed_root.pml4,(uintptr_t)qotom_copy_root.pml4,
        closed_scan,copy_scan,transferred,bytes_match,active_root,4));
    serial_puts(" cpl3-authority=0\n");
    if(accepted!=1 || errors!=0)pre_admission_fail("qotom-copy-root-publication");
#ifdef LEANOS_QOTOM_ENTRY_INTEGRATION
    lab_run_qotom_entry_integration();
#endif
    pre_admission_fail("qotom-entry-integration-pending");
}
