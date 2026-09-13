static __attribute__((noreturn,noinline)) void lab_capture_nosmap_control(void) {
    uint64_t cr0, cr4_before, cr4_after, efer, rflags;
    uint32_t low, high;
    __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4_before));
    __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
                      : "c"(UINT32_C(0xc0000080)));
    efer=(uint64_t)low|((uint64_t)high<<32);
    __asm__ volatile ("pushfq; pop %0" : "=r"(rflags) : : "memory");

    if(leanos_qotom_nosmap_control_query(
            cr0,cr4_before,cr4_before,efer,rflags,0)!=1 ||
       leanos_qotom_nosmap_control_query(
            cr0,cr4_before,cr4_before,efer,rflags,1)!=1)
        pre_admission_fail("qotom-nosmap-controls");

    cr4_after=cr4_before|UINT64_C(0x100000);
    __asm__ volatile ("mov %0, %%cr4" : : "r"(cr4_after) : "memory");
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4_after));
    uint64_t status=leanos_qotom_nosmap_control_query(
        cr0,cr4_before,cr4_after,efer,rflags,2);
    uint64_t errors=leanos_qotom_nosmap_control_query(
        cr0,cr4_before,cr4_after,efer,rflags,3);
    serial_puts("LEANOS-LAB/1 NO-SMAP-CONTROL profile=qotom-copy-roots-v1 status=");
    serial_u64(status==1?0:1);
    serial_puts(" cr0=");serial_u64(cr0);
    serial_puts(" cr4-before=");serial_u64(cr4_before);
    serial_puts(" cr4-after=");serial_u64(cr4_after);
    serial_puts(" efer=");serial_u64(efer);
    serial_puts(" rflags=");serial_u64(rflags);
    serial_puts(" error-mask=");serial_u64(errors);
    serial_puts(" strategy=qotom-copy-roots-v1 max-bytes=");
    serial_u64(leanos_qotom_nosmap_control_query(cr0,cr4_before,cr4_after,efer,rflags,5));
    serial_puts(" max-aliases=");
    serial_u64(leanos_qotom_nosmap_control_query(cr0,cr4_before,cr4_after,efer,rflags,6));
    serial_puts(" reload=mandatory cpl3-authority=");
    serial_u64(leanos_qotom_nosmap_control_query(cr0,cr4_before,cr4_after,efer,rflags,8));
    serial_puts(" closed-root-published=");
    serial_u64(leanos_qotom_nosmap_control_query(cr0,cr4_before,cr4_after,efer,rflags,9));
    serial_puts(" copy-root-published=");
    serial_u64(leanos_qotom_nosmap_control_query(cr0,cr4_before,cr4_after,efer,rflags,10));
    serial_putc('\n');
    if(status!=1 || errors!=0)pre_admission_fail("qotom-nosmap-controls");
#ifdef LEANOS_QOTOM_COPY_ROOT_PUBLICATION
    lab_publish_qotom_copy_roots();
#else
    pre_admission_fail("qotom-copy-roots-pending");
#endif
}
