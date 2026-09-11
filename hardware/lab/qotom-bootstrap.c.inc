/* Lab-only BSP observation. CPUID MSR/APIC bits gate the read; no writes,
 * AP startup, interrupt routing, or runtime authority are introduced. */
static void lab_capture_bootstrap(uint32_t cpuid_edx) {
    uint32_t available = (cpuid_edx & UINT32_C(0x220)) == UINT32_C(0x220);
    uint64_t apic_base = 0;
    if (available) {
        uint32_t low, high;
        __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
                          : "c"(UINT32_C(0x1b)) : "memory");
        apic_base = (uint64_t)high << 32 | low;
    }
    serial_puts("LEANOS-LAB/1 BOOTSTRAP cpuid-edx="); serial_u64(cpuid_edx);
    serial_puts(" available="); serial_u64(available);
    serial_puts(" apic-base="); serial_u64(apic_base); serial_putc('\n');
}
