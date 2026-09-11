/* Lab-only cache/control observation. No MSR, control-register or MMIO writes.
 * The CPU feature gate controls whether IA32_PAT may be sampled; an exception
 * remains terminal under the diagnostic's existing fault policy. */
static void lab_capture_ecam_memory(uint32_t cpuid_edx) {
    uint64_t pat = 0, cr0, cr3, cr4;
    uint32_t available = (cpuid_edx & UINT32_C(0x10020)) == UINT32_C(0x10020);
    if (available) {
        uint32_t low, high;
        __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
                          : "c"(UINT32_C(0x277)) : "memory");
        pat = (uint64_t)high << 32 | low;
    }
    __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
    serial_puts("LEANOS-LAB/1 ECAM-MEMORY cpuid-edx="); serial_u64(cpuid_edx);
    serial_puts(" available="); serial_u64(available);
    serial_puts(" pat="); serial_u64(pat);
    serial_puts(" cr0="); serial_u64(cr0);
    serial_puts(" cr3="); serial_u64(cr3);
    serial_puts(" cr4="); serial_u64(cr4); serial_putc('\n');
}
