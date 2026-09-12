#include "qotom-apic-lvt-window.h"

struct lab_qotom_apic_identity { uint64_t base; uint32_t id; };

static int lab_qotom_lvt_native_controls(
        void *opaque, struct lab_ecam_controls *controls) {
    (void)opaque;
    uint32_t a, b, c, d;
    __asm__ volatile ("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                      : "a"(1u), "c"(0u) : "memory");
    if ((d & UINT32_C(0x10020)) != UINT32_C(0x10020)) return 0;
    uint32_t low, high;
    __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
                      : "c"(UINT32_C(0x277)) : "memory");
    controls->pat = (uint64_t)high << 32 | low;
    __asm__ volatile ("mov %%cr0, %0" : "=r"(controls->cr0));
    __asm__ volatile ("mov %%cr3, %0" : "=r"(controls->cr3));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(controls->cr4));
    __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
                      : "c"(UINT32_C(0xc0000080)) : "memory");
    controls->efer = (uint64_t)high << 32 | low;
    __asm__ volatile ("pushfq; pop %0" : "=r"(controls->rflags) : : "memory");
    return 1;
}

static int lab_qotom_lvt_native_identity(struct lab_qotom_apic_identity *out) {
    uint32_t a, b, c, d;
    __asm__ volatile ("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                      : "a"(0u), "c"(0u) : "memory");
    if (a < 1u) return 0;
    __asm__ volatile ("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                      : "a"(1u), "c"(0u) : "memory");
    if ((d & UINT32_C(0x220)) != UINT32_C(0x220)) return 0;
    uint32_t low, high;
    __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
                      : "c"(UINT32_C(0x1b)) : "memory");
    out->base = (uint64_t)high << 32 | low;
    out->id = b >> 24;
    return 1;
}

static __attribute__((noinline, noipa)) void lab_qotom_lvt_native_invalidate(
        void *opaque, uint64_t address) {
    (void)opaque;
    __asm__ volatile ("invlpg (%0)" : : "r"(address) : "memory");
}

static __attribute__((noinline, noipa)) int lab_qotom_lvt_native_load32(
        void *opaque, uint64_t address, uint32_t *value) {
    (void)opaque;
    *value = *(const volatile uint32_t *)(uintptr_t)address;
    return 1;
}

static __attribute__((noreturn)) void lab_qotom_lvt_native_fault(void *opaque) {
    (void)opaque;
    pre_admission_fail("qotom-platform-pending");
}

static __attribute__((noinline, noipa)) uint64_t lab_sample_qotom_apic_lvt(
        struct lab_qotom_apic_identity *before,
        struct lab_qotom_lvt_sample *sample) {
    struct lab_qotom_lvt_window window = {
        .opaque = NULL,
        .controls = lab_qotom_lvt_native_controls,
        .invalidate = lab_qotom_lvt_native_invalidate,
        .load32 = lab_qotom_lvt_native_load32,
        .fault = lab_qotom_lvt_native_fault,
    };
    struct lab_qotom_apic_identity after = {0,0};
    uint64_t status = 1;
    if (lab_qotom_lvt_native_identity(before) && before->id == 0 &&
        lab_qotom_lvt_arm(&window, page_table_a, BOOT_LEAF_COUNT,
            (uint64_t)page_map_level_4_a, (uint64_t)boot_acpi_mapping_window,
            before->base) && lab_qotom_lvt_read(&window, sample)) {
        status = 2;
        if (lab_qotom_lvt_native_identity(&after) &&
            after.id == before->id && after.base == before->base)
            status = 0;
    }
    return status;
}

static void lab_report_qotom_apic_lvt(
        uint64_t status, const struct lab_qotom_apic_identity *before,
        const struct lab_qotom_lvt_sample *sample) {
    serial_puts("LEANOS-LAB/1 APIC-LVT profile=qotom-lvt-v1 status=");
    serial_u64(status);
    serial_puts(" apic-base="); serial_u64(before->base);
    serial_puts(" executing="); serial_u64(before->id);
    serial_puts(" lint0-first="); serial_u64(sample->lint0_first);
    serial_puts(" lint1-first="); serial_u64(sample->lint1_first);
    serial_puts(" lint0-second="); serial_u64(sample->lint0_second);
    serial_puts(" lint1-second="); serial_u64(sample->lint1_second);
    serial_puts(" stable="); serial_u64(
        sample->lint0_first == sample->lint0_second &&
        sample->lint1_first == sample->lint1_second);
    serial_puts(" routing-authority=0 writes=0 map-restored=1 platform-admitted=0\n");
}

#ifdef LEANOS_QOTOM_LVT_OBSERVATION
static __attribute__((noinline, noipa)) void lab_observe_qotom_apic_lvt(void) {
    struct lab_qotom_apic_identity before = {0,0};
    struct lab_qotom_lvt_sample sample = {0,0,0,0};
    const uint64_t status = lab_sample_qotom_apic_lvt(&before, &sample);
    lab_report_qotom_apic_lvt(status, &before, &sample);
    if (status != 0) pre_admission_fail("qotom-platform-pending");
}
#endif

#ifdef LEANOS_QOTOM_LVT_POLICY
static __attribute__((noinline, noipa)) void lab_enforce_qotom_apic_lvt(void) {
    struct lab_qotom_apic_identity before = {0,0};
    struct lab_qotom_lvt_sample sample = {0,0,0,0};
    const uint64_t status = lab_sample_qotom_apic_lvt(&before, &sample);
    const uint64_t stable = sample.lint0_first == sample.lint0_second &&
                            sample.lint1_first == sample.lint1_second;
    uint64_t policy[6];
    for (uint64_t word = 0; word < 6; ++word)
        policy[word] = leanos_qotom_inherited_lvt_policy_query(
            status,before.base,before.id,sample.lint0_first,sample.lint1_first,
            sample.lint0_second,sample.lint1_second,stable,0,0,1,word);
    lab_report_qotom_apic_lvt(status, &before, &sample);
    const uint64_t accepted = policy[1] == 1 && policy[2] == 0 &&
        policy[3] == 1 && policy[4] == sample.lint0_first &&
        policy[5] == sample.lint1_first;
    const uint64_t rejected = policy[1] == 2 && policy[2] >= 90 &&
        policy[2] <= 97 && policy[3] == 0 && policy[4] == 0 && policy[5] == 0;
    if (policy[0] != 1 || (!accepted && !rejected))
        pre_admission_fail("qotom-lvt-policy-abi");
    serial_puts("LEANOS-LAB/1 APIC-LVT-POLICY profile=qotom-lvt-v1 status=");
    serial_u64(policy[1] == 1 ? 0 : policy[2]);
    serial_puts(" detail="); serial_u64(policy[2]);
    serial_puts(" lint0="); serial_u64(policy[4]);
    serial_puts(" lint1="); serial_u64(policy[5]);
    serial_puts(" policy=");
    serial_puts(policy[3] == 1 ? "masked-inherited" : "rejected");
    serial_puts(" routing-authority=0 writes=0 map-restored=1 platform-admitted=0\n");
    if (!accepted)
        pre_admission_fail("qotom-lvt-policy");
}
#endif
