/* Physical Qotom continuation of the reviewed blocking-IPC scenario.
 *
 * Every entry arrives on the TSS-owned stack, records the incoming subject
 * root in assembly, reloads the closed root, and only then reaches these C
 * dispatchers. The generated capability-reuse and blocking-IPC adapters are
 * the same ones exercised by the q35 scenario. Qotom replaces SMAP with two
 * bounded supervisor-only copy roots: one read-only source view and one
 * writable destination view. No asynchronous interrupt is enabled.
 */

static uint64_t qotom_blocking_step;
static uint64_t qotom_capability_step;
static uint64_t qotom_copy_step;
static uint64_t qotom_saved_a[20];
static uint64_t qotom_saved_b[20];
static uint8_t qotom_blocking_copy_buffer[4];
extern char qotom_blocking_user_a[], qotom_blocking_user_b[];
extern char qotom_blocking_user_a_fault_instruction[],
    qotom_blocking_user_a_fault_recovered[];

static __attribute__((noreturn)) void qotom_blocking_fail(const char *reason) {
    pre_admission_fail(reason);
}

static uint64_t qotom_blocking_root(uint64_t subject) {
    return subject==1?(uint64_t)page_map_level_4_a:
        subject==2?(uint64_t)page_map_level_4_b:0;
}

static uint64_t qotom_blocking_rsp(uint64_t subject) {
    return subject==1?(uint64_t)user_a_stack_top:
        subject==2?(uint64_t)user_b_stack_top:0;
}

static void qotom_copy_frame(uint64_t *destination,const uint64_t *source) {
    for(unsigned i=0;i<20;++i)destination[i]=source[i];
}

static void qotom_initial_a_frame(uint64_t *saved) {
    for(unsigned i=0;i<20;++i)saved[i]=0;
    saved[15]=(uint64_t)qotom_blocking_user_a;
    saved[16]=UINT64_C(0x23);
    saved[17]=UINT64_C(2);
    saved[18]=(uint64_t)user_a_stack_top;
    saved[19]=UINT64_C(0x1b);
}

static void qotom_require_user_frame(const uint64_t *saved,uint64_t subject,
        uint64_t allow_df) {
    uint64_t active_root;
    __asm__ volatile("mov %%cr3,%0":"=r"(active_root));
    active_root&=QOTOM_ROOT_ADDRESS_MASK;
    uint64_t incoming=qotom_entry_observed_root&QOTOM_ROOT_ADDRESS_MASK;
    uint64_t expected=qotom_blocking_root(subject);
    uint64_t prohibited=(UINT64_C(1)<<8)|(UINT64_C(1)<<9)|
        (UINT64_C(3)<<12)|(UINT64_C(1)<<14)|(UINT64_C(1)<<16)|
        (UINT64_C(1)<<17)|(UINT64_C(1)<<18)|(UINT64_C(1)<<19)|
        (UINT64_C(1)<<20)|(UINT64_C(1)<<21);
    if(!allow_df)prohibited|=UINT64_C(1)<<10;
    if(!saved || subject!=current_subject || expected==0 ||
       incoming!=expected || active_root!=qotom_entry_closed_root ||
       saved[16]!=UINT64_C(0x23) || saved[19]!=UINT64_C(0x1b) ||
       saved[18]!=qotom_blocking_rsp(subject) ||
       (saved[17]&UINT64_C(2))==0 || (saved[17]&prohibited)!=0 ||
       (allow_df && (saved[17]&(UINT64_C(1)<<10))==0))
        qotom_blocking_fail("qotom-blocking-frame");
}

static int qotom_blocking_canaries(const uint64_t *saved,
        uint64_t expected_rdx) {
    return saved[0]==UINT64_C(0x150015) &&
        saved[1]==UINT64_C(0x140014) &&
        saved[2]==UINT64_C(0x51a7e51a7e51a7e5) &&
        saved[3]==UINT64_C(0xc0dec0dec0dec0de) &&
        saved[4]==UINT64_C(0x110011) && saved[5]==UINT64_C(0x100010) &&
        saved[6]==UINT64_C(0x090009) && saved[7]==UINT64_C(0x080008) &&
        saved[8]==UINT64_C(0x070007) && saved[9]==UINT64_C(0x060006) &&
        saved[10]==UINT64_C(0x050005) && saved[11]==expected_rdx;
}

static uint64_t qotom_alias_address(uint64_t address,
        const struct qotom_copy_alias *aliases) {
    uint64_t frame=address>>12;
    for(unsigned i=0;i<QOTOM_ROOT_MAX_ALIASES;++i)
        if(aliases[i].frame==frame)
            return aliases[i].page*UINT64_C(4096)+(address&UINT64_C(4095));
    qotom_blocking_fail("qotom-blocking-copy-address");
}

static void qotom_blocking_copy_in(uint64_t address,uint64_t count) {
    struct qotom_copy_operand operands[4];
    if(count!=4 || address!=(uint64_t)user_a_stack+4094u)
        qotom_blocking_fail("qotom-blocking-copy-in-range");
    for(unsigned i=0;i<4;++i)operands[i]=(struct qotom_copy_operand){
        qotom_alias_address(address+i,qotom_aliases),
        (uint64_t)&qotom_blocking_copy_buffer[i]};
    if(leanos_copy_root_transfer(qotom_entry_closed_root,
            (uint64_t)qotom_copy_root.pml4,operands,4)!=4)
        qotom_blocking_fail("qotom-blocking-copy-in");
    if(qotom_blocking_copy_buffer[0]!=0x5a ||
       qotom_blocking_copy_buffer[1]!=0xa5 ||
       qotom_blocking_copy_buffer[2]!=0x3c ||
       qotom_blocking_copy_buffer[3]!=0xc3)
        qotom_blocking_fail("qotom-blocking-copy-in-data");
}

static void qotom_blocking_copy_out(uint64_t address,uint64_t count) {
    struct qotom_copy_operand operands[4];
    if(count!=4 || address!=(uint64_t)user_a_stack+4110u ||
       !qotom_alias_root_exact(&qotom_copy_out_root,
           qotom_copy_out_aliases,qotom_root_result.protected_count))
        qotom_blocking_fail("qotom-blocking-copy-out-range");
    for(unsigned i=0;i<4;++i)operands[i]=(struct qotom_copy_operand){
        (uint64_t)&qotom_blocking_copy_buffer[i],
        qotom_alias_address(address+i,qotom_copy_out_aliases)};
    if(leanos_copy_root_transfer(qotom_entry_closed_root,
            (uint64_t)qotom_copy_out_root.pml4,operands,4)!=4)
        qotom_blocking_fail("qotom-blocking-copy-out");
}

static uint64_t qotom_blocking_capability(uint64_t *saved,uint64_t number) {
    uint64_t argument=saved[13];
    if(number==10 && qotom_capability_step==0) {
        uint64_t got=leanos_capability_reuse_demo(0,1,argument,saved[12],saved[11]);
        uint64_t event=got&0xffu,next=(got>>8)&0xffu,evidence=(got>>16)&0xffu;
        uint64_t slot=(got>>24)&0xffffu,generation=(got>>40)&0xffffu;
        uint64_t endpoint=(got>>56)&0xffu,word=generation*65536u+slot;
        if(got!=oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_INITIAL].expected ||
           event!=1 || next!=1 || evidence!=11 || word!=argument)
            qotom_blocking_fail("qotom-blocking-cap-initial");
        qotom_capability_step=next;
        serial_puts(LEANOS_SERIAL_9_CAPREUSE " event=initial subject=2 handle=");
        serial_u64(word);serial_puts(" endpoint=");serial_u64(endpoint);
        serial_puts(" accepted=1\n");

        got=leanos_capability_reuse_demo(qotom_capability_step,1,
            argument,saved[12],saved[11]);
        event=got&0xffu;next=(got>>8)&0xffu;evidence=(got>>16)&0xffu;
        slot=(got>>24)&0xffffu;generation=(got>>40)&0xffffu;
        endpoint=(got>>56)&0xffu;word=generation*65536u+slot;
        if(got!=oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_CLEARED_SLOT].expected ||
           event!=2 || next!=2 || evidence!=15)
            qotom_blocking_fail("qotom-blocking-cap-replace");
        qotom_capability_step=next;
        serial_puts(LEANOS_SERIAL_9_CAPREUSE " event=clear slot=0 old-generation=2 result=PASS\n");
        serial_puts(LEANOS_SERIAL_9_CAPREUSE " event=install slot=0 generation=3 endpoint=11 result=PASS\n");
        return word;
    }
    if(number==11 && qotom_capability_step==2) {
        uint64_t got=leanos_capability_reuse_demo(2,1,argument,saved[12],saved[11]);
        uint64_t next=(got>>8)&0xffu,evidence=(got>>16)&0xffu;
        uint64_t slot=(got>>24)&0xffffu,generation=(got>>40)&0xffffu;
        uint64_t word=generation*65536u+slot,endpoint=(got>>56)&0xffu;
        if(got!=oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_STALE_GENERATION].expected ||
           (got&0xffu)!=3 || next!=3 || evidence!=8 || word!=argument)
            qotom_blocking_fail("qotom-blocking-cap-stale");
        qotom_capability_step=next;
        serial_puts(LEANOS_SERIAL_9_CAPREUSE " event=stale-replay subject=2 handle=");
        serial_u64(word);serial_puts(" rejected=1\n");
        serial_puts(LEANOS_SERIAL_9_CAPREUSE " event=unchanged endpoint=");
        serial_u64(endpoint);serial_puts(" mailbox=empty result=PASS\n");
        return 0;
    }
    if(number==12 && qotom_capability_step==3) {
        uint64_t got=leanos_capability_reuse_demo(3,1,argument,saved[12],saved[11]);
        uint64_t next=(got>>8)&0xffu,evidence=(got>>16)&0xffu;
        uint64_t slot=(got>>24)&0xffffu,generation=(got>>40)&0xffffu;
        uint64_t word=generation*65536u+slot,endpoint=(got>>56)&0xffu;
        if(got!=oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_FRESH_GENERATION].expected ||
           (got&0xffu)!=4 || next!=4 || evidence!=5 || word!=argument)
            qotom_blocking_fail("qotom-blocking-cap-fresh");
        qotom_capability_step=next;
        serial_puts(LEANOS_SERIAL_9_CAPREUSE " event=fresh subject=2 handle=");
        serial_u64(word);serial_puts(" endpoint=");serial_u64(endpoint);
        serial_puts(" accepted=1\n");
        serial_puts(LEANOS_SERIAL_9_CAPREUSE " status=PASS stale-effects=0 fresh-effects=1\n");
        return 1;
    }
    qotom_blocking_fail("qotom-blocking-cap-sequence");
}

static uint64_t qotom_blocking_dispatch(uint64_t *saved) {
    uint64_t number=saved?saved[14]:UINT64_MAX;
    qotom_require_user_frame(saved,current_subject,number==4);

    if(current_subject==2 && number>=10 && number<=12) {
        saved[14]=qotom_blocking_capability(saved,number);
        saved[17]&=~((UINT64_C(1)<<10)|(UINT64_C(1)<<18));
        return qotom_entry_subject_root;
    }
    if(current_subject==2 && number==7 && qotom_blocking_step==0) {
        if(qotom_capability_step!=4 ||
           !qotom_blocking_canaries(saved,UINT64_C(0x040004)) ||
           saved[13]!=0 || saved[12]!=0)
            qotom_blocking_fail("qotom-blocking-block-frame");
        uint64_t got=leanos_blocking_ipc_demo(0,1,2,0x4c45414e,0x4f53);
        if(got!=oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_BLOCK_B].expected)
            qotom_blocking_fail("qotom-blocking-model-block");
        qotom_copy_frame(qotom_saved_b,saved);
        qotom_initial_a_frame(saved);
        qotom_blocking_step=2;
        current_subject=1;
        qotom_entry_subject_root=(uint64_t)page_map_level_4_a;
        serial_puts(LEANOS_SERIAL_10_IPC " event=block subject=2 endpoint=10 empty=1 runnable=0 result=PASS\n");
        serial_puts(LEANOS_SERIAL_8_PAGING " root=A selected=1 resumed=1 result=PASS\n");
        serial_puts(LEANOS_SERIAL_10_IPC " event=dispatch subject=1 address-space=1 blocked-subject=2 trusted=1\n");
        return qotom_entry_subject_root;
    }
    if(current_subject==1 && number==4 && qotom_blocking_step==2) {
        if(saved[13]==0 && qotom_copy_step==0) {
            qotom_blocking_copy_in(saved[12],saved[11]);
            qotom_copy_step=1;saved[14]=0;
            serial_puts(LEANOS_SERIAL_6_COPY " direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS\n");
        } else if(saved[13]==1 && qotom_copy_step==1) {
            qotom_blocking_copy_out(saved[12],saved[11]);
            qotom_copy_step=2;saved[14]=0;
            serial_puts(LEANOS_SERIAL_6_COPY " direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS\n");
        } else qotom_blocking_fail("qotom-blocking-copy-sequence");
        saved[17]&=~((UINT64_C(1)<<10)|(UINT64_C(1)<<18));
        return (uint64_t)page_map_level_4_a;
    }
    if(current_subject==1 && number==8 && qotom_blocking_step==2) {
        if(qotom_copy_step!=2 || saved[13]!=UINT64_C(0x4c45414e) ||
           saved[12]!=UINT64_C(0x4f53) || saved[11]!=0)
            qotom_blocking_fail("qotom-blocking-send-frame");
        uint64_t sent=leanos_blocking_ipc_demo(1,2,1,saved[13],saved[12]);
        uint64_t dispatched=leanos_blocking_ipc_demo(2,3,1,saved[13],saved[12]);
        if(sent!=oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_SEND_WAKE_B].expected ||
           dispatched!=oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_DISPATCH_B].expected)
            qotom_blocking_fail("qotom-blocking-model-send");
        qotom_copy_frame(qotom_saved_a,saved);
        qotom_copy_frame(saved,qotom_saved_b);
        saved[14]=UINT64_C(0x4c45414e);
        saved[13]=UINT64_C(0x4f53);
        saved[12]=UINT64_C(1);
        qotom_blocking_step=4;
        current_subject=2;
        qotom_entry_subject_root=(uint64_t)page_map_level_4_b;
        serial_puts(LEANOS_SERIAL_10_IPC " event=send sender=1 endpoint=10 payload0=1279607118 payload1=20307 accepted=1\n");
        serial_puts(LEANOS_SERIAL_10_IPC " event=wake subject=2 ready-insertions=1 reserved=1 result=PASS\n");
        serial_puts(LEANOS_SERIAL_8_PAGING " root=B selected=1 result=PASS\n");
        serial_puts(LEANOS_SERIAL_10_IPC " event=dispatch subject=2 address-space=2 reservation=owned trusted=1\n");
        return qotom_entry_subject_root;
    }
    if(current_subject==2 && number==9 && qotom_blocking_step==4) {
        if(!qotom_blocking_canaries(saved,UINT64_C(1)) ||
           saved[13]!=UINT64_C(0x4c45414e) ||
           saved[12]!=UINT64_C(0x4f53) || saved[11]!=1 ||
           qotom_saved_a[15]==0 || qotom_saved_b[15]==0)
            qotom_blocking_fail("qotom-blocking-deliver-frame");
        uint64_t got=leanos_blocking_ipc_demo(3,4,2,
            saved[13],saved[12]);
        if(got!=oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_DELIVER_B].expected)
            qotom_blocking_fail("qotom-blocking-model-delivery");
        serial_puts(LEANOS_SERIAL_10_IPC " event=deliver receiver=2 endpoint=10 sender=1 payload0=1279607118 payload1=20307 exact=1 canaries=preserved\n");
        serial_puts(LEANOS_SERIAL_10_FINAL " status=PASS blocks=1 wakes=1 deliveries=1\n");
        for(;;)__asm__ volatile("cli; hlt");
    }
    qotom_blocking_fail("qotom-blocking-syscall-sequence");
}

uint64_t qotom_blocking_page_fault_dispatch(uint64_t *frame) {
    uint64_t active_root;
    const uint64_t prohibited=(UINT64_C(1)<<8)|(UINT64_C(1)<<9)|
        (UINT64_C(1)<<10)|(UINT64_C(3)<<12)|(UINT64_C(1)<<14)|
        (UINT64_C(1)<<17)|(UINT64_C(1)<<18)|(UINT64_C(1)<<19)|
        (UINT64_C(1)<<20)|(UINT64_C(1)<<21);
    __asm__ volatile("mov %%cr3,%0":"=r"(active_root));
    active_root&=QOTOM_ROOT_ADDRESS_MASK;
    if(!frame || current_subject!=1 || qotom_blocking_step!=2 ||
       qotom_copy_step!=2 || frame[0]!=0 || frame[16]!=5 ||
       frame[17]!=(uint64_t)qotom_blocking_user_a_fault_instruction ||
       frame[18]!=0x23 || frame[20]!=(uint64_t)user_a_stack_top ||
       frame[21]!=0x1b || (frame[19]&UINT64_C(2))==0 ||
       (frame[19]&(UINT64_C(1)<<16))==0 || (frame[19]&prohibited)!=0 ||
       frame[1]!=0 || frame[2]!=0 || frame[3]!=0 || frame[4]!=0 ||
       frame[5]!=0 || frame[6]!=0 || frame[7]!=0 || frame[8]!=0 ||
       frame[9]!=0 || frame[10]!=0 || frame[11]!=0 || frame[12]!=4 ||
       frame[13]!=(uint64_t)user_a_stack+4110u || frame[14]!=1 ||
       frame[15]!=0 ||
       (qotom_entry_observed_root&QOTOM_ROOT_ADDRESS_MASK)!=(uint64_t)page_map_level_4_a ||
       active_root!=qotom_entry_closed_root)
        qotom_blocking_fail("qotom-blocking-page-fault");
    frame[17]=(uint64_t)qotom_blocking_user_a_fault_recovered;
    frame[19]&=~((UINT64_C(1)<<10)|(UINT64_C(1)<<18));
    serial_puts(LEANOS_SERIAL_11_USER_FAULT " vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS\n");
    return (uint64_t)page_map_level_4_a;
}

static int qotom_blocking_gate_exact(unsigned vector, const void *handler,
        uint8_t attributes) {
    return idt_target(&idt[vector])==(uint64_t)handler &&
        idt[vector].selector==0x08 && idt[vector].ist==0 &&
        idt[vector].attributes==attributes && idt[vector].zero==0;
}

static __attribute__((noreturn,noinline)) void lab_run_qotom_blocking_ipc(
        uint64_t entry_checkpoint) {
    uint64_t active_root,flags;
    __asm__ volatile("mov %%cr3,%0":"=r"(active_root));
    __asm__ volatile("pushfq; pop %0":"=r"(flags)::"memory");
    active_root&=QOTOM_ROOT_ADDRESS_MASK;
    if(active_root!=qotom_entry_closed_root || (flags&(UINT64_C(1)<<9))!=0 ||
       !qotom_closed_root_exact(qotom_root_result.protected_count) ||
       !qotom_copy_root_exact(qotom_root_result.protected_count) ||
       !qotom_alias_root_exact(&qotom_copy_out_root,qotom_copy_out_aliases,
           qotom_root_result.protected_count))
        qotom_blocking_fail("qotom-blocking-roots");
    qotom_blocking_step=0;qotom_capability_step=0;qotom_copy_step=0;
    for(unsigned i=0;i<20;++i)qotom_saved_a[i]=qotom_saved_b[i]=0;
    qotom_blocking_active=1;
    current_subject=2;
    set_gate(14,qotom_entry_isr14,0,0x8e);
    uint64_t syscall_gate=qotom_blocking_gate_exact(0x80,qotom_entry_isr80,0xee);
    uint64_t page_fault_gate=qotom_blocking_gate_exact(14,qotom_entry_isr14,0x8e);
    uint64_t timer_gate_absent=idt_target(&idt[32])==0 &&
        idt[32].selector==0 && idt[32].ist==0 &&
        idt[32].attributes==0 && idt[32].zero==0;
    uint64_t pic_masked=in8(0x21)==0xff && in8(0xa1)==0xff;
    uint64_t admitted=leanos_qotom_blocking_ipc_integration_query(
        1,1,entry_checkpoint,qotom_entry_closed_root,
        (uint64_t)qotom_copy_root.pml4,(uint64_t)qotom_copy_out_root.pml4,
        qotom_closed_root_exact(qotom_root_result.protected_count),
        qotom_copy_root_exact(qotom_root_result.protected_count),
        qotom_alias_root_exact(&qotom_copy_out_root,qotom_copy_out_aliases,
            qotom_root_result.protected_count),
        syscall_gate,page_fault_gate,timer_gate_absent,pic_masked,2,1,1);
    uint64_t errors=leanos_qotom_blocking_ipc_integration_query(
        1,1,entry_checkpoint,qotom_entry_closed_root,
        (uint64_t)qotom_copy_root.pml4,(uint64_t)qotom_copy_out_root.pml4,
        1,1,1,syscall_gate,page_fault_gate,timer_gate_absent,pic_masked,2,1,2);
    uint64_t authority=leanos_qotom_blocking_ipc_integration_query(
        1,1,entry_checkpoint,qotom_entry_closed_root,
        (uint64_t)qotom_copy_root.pml4,(uint64_t)qotom_copy_out_root.pml4,
        1,1,1,syscall_gate,page_fault_gate,timer_gate_absent,pic_masked,2,1,3);
    if(admitted!=1 || errors!=0 || authority!=1)
        qotom_blocking_fail("qotom-blocking-profile");
    serial_puts("LEANOS-LAB/1 QOTOM-IPC-READY profile=qotom-blocking-ipc-v1 subjects=2 interrupts=masked timer-gate=absent pic=masked copy-in=readonly-root copy-out=writable-root cpl3-authority=1\n");
    serial_puts(LEANOS_SERIAL_10_IPC " event=enter subject=2 address-space=2 cpl=3 endpoint=10\n");
    qotom_entry_start((uint64_t)page_map_level_4_b,qotom_entry_closed_root,
        qotom_blocking_user_b,user_b_stack_top);
}
