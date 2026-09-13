extern void qotom_entry_start(uint64_t subject_root, uint64_t closed_root,
    const void *user_rip, const void *user_rsp) __attribute__((noreturn));
extern void qotom_entry_isr2(void), qotom_entry_isr6(void),
    qotom_entry_isr8(void), qotom_entry_isr13(void), qotom_entry_isr14(void),
    qotom_entry_isr80(void);
extern char qotom_entry_user[], qotom_entry_user_after_first[],
    qotom_entry_user_after_second[];

uint64_t qotom_entry_closed_root;
uint64_t qotom_entry_subject_root;
volatile uint64_t qotom_entry_observed_root;
static uint64_t qotom_entry_completed_returns;

void __attribute__((noreturn)) qotom_entry_gp_dispatch(const uint64_t *frame) {
    uint64_t active_root;
    __asm__ volatile("mov %%cr3,%0":"=r"(active_root));
    active_root&=QOTOM_ROOT_ADDRESS_MASK;
    serial_puts("LEANOS-LAB/1 QOTOM-ENTRY-GP profile=qotom-copy-roots-v1 root=");
    serial_u64(active_root);
    serial_puts(" error=");serial_u64(frame[0]);
    serial_puts(" rip=");serial_u64(frame[1]);
    serial_puts(" cs=");serial_u64(frame[2]);
    serial_puts(" rflags=");serial_u64(frame[3]);
    serial_puts(" tail0=");serial_u64(frame[4]);
    serial_puts(" tail1=");serial_u64(frame[5]);
    serial_puts(" cpl3-authority=0\n");
    pre_admission_fail("qotom-entry-gp");
}

static int qotom_entry_registers_exact(const uint64_t *saved) {
    return saved[0]==UINT64_C(0xffff) && saved[1]==UINT64_C(0xeeee) &&
        saved[2]==UINT64_C(0x51a7e51a7e51a7e5) &&
        saved[3]==UINT64_C(0xc0dec0dec0dec0de) &&
        saved[4]==UINT64_C(0xbbbb) && saved[5]==UINT64_C(0xaaaa) &&
        saved[6]==UINT64_C(0x9999) && saved[7]==UINT64_C(0x8888) &&
        saved[8]==UINT64_C(0x7777) && saved[9]==UINT64_C(0x6666) &&
        saved[10]==UINT64_C(0x5555) && saved[11]==UINT64_C(0x4444) &&
        saved[12]==UINT64_C(0x3333) && saved[13]==UINT64_C(0x2222);
}

uint64_t qotom_entry_dispatch(uint64_t *saved) {
    uint64_t active_root,flags;
    __asm__ volatile("mov %%cr3,%0":"=r"(active_root));
    __asm__ volatile("pushfq; pop %0":"=r"(flags)::"memory");
    active_root&=QOTOM_ROOT_ADDRESS_MASK;
    uint64_t user_rsp=(uint64_t)user_a_stack_top;
    uint64_t expected_rip=qotom_entry_completed_returns==0
        ?(uint64_t)qotom_entry_user_after_first
        :(uint64_t)qotom_entry_user_after_second;
    uint64_t expected_call=qotom_entry_completed_returns==0?UINT64_C(0x51):UINT64_C(0x52);
    if(!saved || active_root!=qotom_entry_closed_root ||
       (qotom_entry_observed_root&QOTOM_ROOT_ADDRESS_MASK)!=qotom_entry_subject_root ||
       qotom_entry_subject_root!=(uint64_t)page_map_level_4_a ||
       qotom_entry_closed_root!=(uint64_t)qotom_closed_root.pml4 ||
       (flags&((UINT64_C(1)<<9)|(UINT64_C(1)<<10)|(UINT64_C(1)<<18)))!=0 ||
       !qotom_entry_registers_exact(saved) || saved[14]!=expected_call ||
       saved[15]!=expected_rip || saved[16]!=UINT64_C(0x23) ||
       (saved[17]&UINT64_C(0x202))!=UINT64_C(0x202) ||
       saved[18]!=user_rsp || saved[19]!=UINT64_C(0x1b))
        pre_admission_fail("qotom-entry-frame");
    if(qotom_entry_completed_returns==0) {
        qotom_entry_completed_returns=1;
        saved[14]=UINT64_C(0x51525354);
        return qotom_entry_subject_root;
    }
    uint64_t accepted=leanos_qotom_entry_integration_query(
        2,1,qotom_entry_observed_root&QOTOM_ROOT_ADDRESS_MASK,
        qotom_entry_closed_root,active_root,1,15,1,1,1);
    uint64_t errors=leanos_qotom_entry_integration_query(
        2,1,qotom_entry_observed_root&QOTOM_ROOT_ADDRESS_MASK,
        qotom_entry_closed_root,active_root,1,15,1,1,2);
    serial_puts("LEANOS-LAB/1 QOTOM-ENTRY profile=qotom-copy-roots-v1 status=");
    serial_u64(accepted==1?0:1);
    serial_puts(" entries=2 returns=1 incoming-root=");
    serial_u64(qotom_entry_observed_root&QOTOM_ROOT_ADDRESS_MASK);
    serial_puts(" closed-root=");serial_u64(qotom_entry_closed_root);
    serial_puts(" active-root=");serial_u64(active_root);
    serial_puts(" frame=1 gprs=15 close-readback=1 return-reload=1 error-mask=");
    serial_u64(errors);
    serial_puts(" entry-contract=");serial_u64(accepted);
    serial_puts(" cpl3-authority=0\n");
    if(accepted!=1 || errors!=0)pre_admission_fail("qotom-entry-contract");
    pre_admission_fail("qotom-exception-integration-pending");
}

static __attribute__((noreturn,noinline)) void lab_run_qotom_entry_integration(void) {
    uint64_t active_root,flags,cr4;
    __asm__ volatile("mov %%cr3,%0":"=r"(active_root));
    __asm__ volatile("pushfq; pop %0":"=r"(flags)::"memory");
    __asm__ volatile("mov %%cr4,%0":"=r"(cr4));
    active_root&=QOTOM_ROOT_ADDRESS_MASK;
    qotom_entry_closed_root=(uint64_t)qotom_closed_root.pml4;
    qotom_entry_subject_root=(uint64_t)page_map_level_4_a;
    qotom_entry_observed_root=0;
    qotom_entry_completed_returns=0;
    if(active_root!=qotom_entry_closed_root ||
       qotom_root_result.protected_count!=5 ||
       (flags&(UINT64_C(1)<<9))!=0 || (cr4&UINT64_C(0x20080))!=0 ||
       qotom_entry_subject_root==0 || (qotom_entry_subject_root&UINT64_C(0xfff))!=0 ||
       qotom_entry_subject_root>=UINT64_C(0x1000000) ||
       qotom_entry_subject_root==qotom_entry_closed_root ||
       !qotom_closed_root_exact(5) || !qotom_copy_root_exact(5))
        pre_admission_fail("qotom-entry-roots");

    privilege_init();
    for(unsigned vector=0;vector<256;++vector)
        idt[vector]=(struct idt_entry){0};
    set_gate(2,qotom_entry_isr2,2,0x8e);
    set_gate(6,qotom_entry_isr6,0,0x8e);
    set_gate(8,qotom_entry_isr8,1,0x8e);
    set_gate(13,qotom_entry_isr13,0,0x8e);
    set_gate(14,qotom_entry_isr14,0,0x8e);
    set_gate(0x80,qotom_entry_isr80,0,0xee);
    current_subject=1;
    serial_puts("LEANOS-LAB/1 QOTOM-ENTRY-READY profile=qotom-copy-roots-v1 subject=1 address-space=1 gates=2,6,8,13,14,128 root=closed cpl3-authority=0\n");
    qotom_entry_start(qotom_entry_subject_root,qotom_entry_closed_root,
        qotom_entry_user,user_a_stack_top);
}
