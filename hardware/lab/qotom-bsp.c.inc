/* Root-selected immutable copies already exist when this diagnostic runs. */
#include "qotom_bsp_consumer.h"
static void lab_check_bsp(uint32_t copied_count) {
    const struct copied_acpi_sdt *madt = select_unique_copied_madt(copied_count);
    validate_generated_madt_envelope(madt);
    if (madt->length <= 44u) handoff_fail("lab-bsp-madt-length");
    const uint32_t executing = observe_executing_apic_id();
    uint32_t a, b, c, d;
    __asm__ volatile ("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                      : "a"(1u), "c"(0u) : "memory");
    uint64_t available = (d & UINT32_C(0x220)) == UINT32_C(0x220);
    uint64_t apic_base = 0;
    if (available) {
        uint32_t low, high;
        __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
                          : "c"(UINT32_C(0x1b)) : "memory");
        apic_base = (uint64_t)high << 32 | low;
    }
    const struct qotom_bsp_observation observation = {
        executing, d, available, apic_base, b >> 24
    };
    const struct qotom_bsp_result result = qotom_bind_validated_madt_entries(
        madt->bytes + 44u, madt->length - 44u, &observation);
    /* Record the actual sample as well as the result, so replay need not
       substitute the earlier bootstrap sample or expected register values. */
    serial_puts("LEANOS-LAB/1 NATIVE-BSP profile=qotom-bsp-v1 madt=");
    serial_u64(madt->physical_address);
    serial_puts(" length="); serial_u64(madt->length);
    serial_puts(" executing="); serial_u64(observation.executing);
    serial_puts(" cpuid-edx="); serial_u64(observation.cpuid_edx);
    serial_puts(" available="); serial_u64(observation.available);
    serial_puts(" apic-base="); serial_u64(observation.apic_base);
    serial_puts(" sample-id="); serial_u64(observation.sample_id);
    serial_puts(" status="); serial_u64(result.status);
    serial_puts(" detail="); serial_u64(result.detail);
    serial_puts(" offset="); serial_u64(result.offset);
    serial_puts(" admitted-id="); serial_u64(result.apic_id);
    serial_puts(" count="); serial_u64(result.processor_count);
    serial_puts(" bound-base="); serial_u64(result.apic_base);
    serial_puts(" platform-admitted=0\n");
    if (result.status) pre_admission_fail("qotom-native-bsp");
}
