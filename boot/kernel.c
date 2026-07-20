#include <stdint.h>
#include "corpus.h"
#if defined(LEANOS_BOOT_PAGE_PLAN_HEADER)
#include LEANOS_BOOT_PAGE_PLAN_HEADER
#elif defined(LEANOS_DF_MAP_GUARD)
#include "boot-page-plan-guard.h"
#elif defined(LEANOS_DOUBLE_FAULT_PROBE)
#include "boot-page-plan-double-fault.h"
#else
#include "boot-page-plan.h"
#endif

#define COM1 0x3f8u
#define DEBUG_EXIT 0xf4u
#define PCI_CONFIG_ADDRESS 0xcf8u
#define PCI_CONFIG_DATA 0xcfcu
#define PCI_COMMAND_BUS_MASTER (1u << 2)
#define PCI_COMMAND_MODEL_MASK 0x07ffu

extern uint64_t leanos_boot_transition(uint64_t state, uint64_t command);
extern uint64_t leanos_syscall_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_ipc_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_preemption_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_resumable_preemption_demo(uint64_t, uint64_t, uint64_t,
                                                  uint64_t, uint64_t);
extern uint64_t leanos_boot_allocation_check(uint64_t, uint64_t, uint64_t,
                                             uint64_t, uint64_t);
extern uint64_t leanos_user_return_demo(uint64_t, uint64_t, uint64_t,
                                        uint64_t, uint64_t);
extern uint64_t leanos_blocking_ipc_demo(uint64_t, uint64_t, uint64_t,
                                          uint64_t, uint64_t);
extern uint64_t leanos_capability_reuse_demo(uint64_t, uint64_t, uint64_t,
                                              uint64_t, uint64_t);
extern uint64_t leanos_entry_demo(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_extended_state_denial_demo(uint64_t, uint64_t, uint64_t,
                                                   uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_privilege_entry_control_demo(uint64_t, uint64_t, uint64_t,
                                                     uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_fault_dispatch_demo(uint64_t, uint64_t, uint64_t,
                                            uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_direct_port_io_demo(uint64_t, uint64_t, uint64_t,
                                            uint64_t, uint64_t, uint64_t);
extern uint64_t gdt64[];
extern void load_tss(void);
extern void read_fast_entry_msrs(uint64_t state[8]);
extern void enable_smep(void);
extern void run_smap_probe(void);
extern void smap_copy_from(void *, const void *, uint64_t);
extern void smap_copy_to(void *, const void *, uint64_t);
extern void smap_omit_cleanup_probe(void);
extern void smap_force_clac(void);
extern void run_wp_probe(void);
extern void run_smep_probe(void);
extern void enter_user(void *, void *);
extern void isr80(void);
extern void isr6(void);
extern void isr7(void);
extern void isr8(void);
extern void isr13(void);
extern void isr14(void);
extern void isr32(void);
extern void run_double_fault_probe(void);
extern char user_a_entry[], user_a_stack_top[];
extern const uint64_t extended_state_probe_class;
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
extern const uint8_t user_a_extended_state_probe[];
#endif
extern char user_a_stack[];
extern char user_a_fault_instruction[], user_a_fault_recovered[];
extern char user_b_entry[];
extern char user_b_stack[], user_b_stack_top[];
extern uint64_t saved_context_a[], saved_context_b[];
extern uint64_t initial_context_b[];
extern const uint64_t saved_context_owner_a, saved_context_owner_b;
extern uint64_t saved_context_a_original_flags, saved_context_a_original_rsp;
extern uint64_t saved_context_b_original_flags, saved_context_b_original_rsp;
extern uint64_t saved_context_a_original_rip, saved_context_b_original_rip;
extern char wp_probe_instruction[], wp_probe_recovered[], wp_probe_target[];
extern char smep_probe_recovered[];
extern char __boot_image_start[], __boot_image_end[];
extern char __df_ist_stack_start[], __df_ist_stack_end[];
extern char __df_ist_guard_start[], __df_ist_guard_end[];
extern char __entry_stack_guard_start[], __entry_stack_guard_end[];
extern char __entry_stack_start[], __entry_stack_end[];
extern char __kernel_text_start[], __kernel_text_end[];
extern char boot_stack[], boot_stack_top[];
extern char __user_a_text_start[], __user_a_text_end[];
extern char __user_a_stack_start[], __user_a_stack_end[];
extern char __user_b_text_start[], __user_b_text_end[];
extern char __user_b_stack_start[], __user_b_stack_end[];
extern uint64_t page_map_level_4_a[], page_directory_pointer_a[];
extern uint64_t page_directory_a[], page_table_a[];
extern uint64_t page_map_level_4_b[], page_directory_pointer_b[];
extern uint64_t page_directory_b[], page_table_b[];

#define MULTIBOOT2_RUNTIME_MAGIC 0x36d76289u
#define BOOT_ACCESSIBLE_LIMIT (16u * 1024u * 1024u)
#define MAX_HANDOFF_BYTES 65536u
#define MAX_MMAP_ENTRIES 128u
#define PAGE_BYTES 4096u
#ifndef LEANOS_RETURN_CORRUPTION_MODE
#define LEANOS_RETURN_CORRUPTION_MODE 0
#endif
#define BOOT_PT_COUNT 8u
#define BOOT_LEAF_COUNT (512u * BOOT_PT_COUNT)
#define PTE_PRESENT 1ull
#define PTE_WRITABLE 2ull
#define PTE_USER 4ull
#define PTE_ACCESSED (1ull << 5)
#define PTE_DIRTY (1ull << 6)
#define PTE_NX (1ull << 63)
#define PTE_ADDRESS 0x000ffffffffff000ull

struct __attribute__((packed)) mb2_tag { uint32_t type, size; };
struct __attribute__((packed)) mb2_mmap_tag {
    uint32_t type, size, entry_size, entry_version;
};
struct __attribute__((packed)) mb2_mmap_entry {
    uint64_t base, length; uint32_t type, reserved;
};

static uint8_t boot_frames[BOOT_ACCESSIBLE_LIMIT / PAGE_BYTES];
static volatile uint64_t published_boot_object;

struct __attribute__((packed)) idt_entry {
    uint16_t low, selector; uint8_t ist, attributes; uint16_t middle; uint32_t high, zero;
};
struct __attribute__((packed)) descriptor { uint16_t limit; uint64_t base; };
struct __attribute__((packed)) tss64 {
    uint32_t reserved0; uint64_t rsp0, rsp1, rsp2; uint64_t reserved1;
    uint64_t ist[7]; uint64_t reserved2; uint16_t reserved3, iomap;
};
static struct idt_entry idt[256] __attribute__((aligned(16)));
static struct tss64 tss;
static uint8_t entry_stack[16384]
    __attribute__((used, section(".entry.stack"), aligned(PAGE_BYTES)));
static unsigned preemption_step;
uint64_t current_subject = 1;
/* Concrete image of the bounded state consumed and published by
   ExtendedState.dispatchDenied.  Bits are indexed by subject identity. */
struct extended_state_authority {
    uint64_t live;
    uint64_t ready;
    uint64_t current;
    uint64_t contexts;
    uint64_t active;
};
static struct extended_state_authority extended_state_authority = {
    (1ull << 1) | (1ull << 2), 1ull << 2, 1, 1ull << 2, 1
};
uint64_t extended_state_selected_cr3;
static unsigned timer_accepted;
static unsigned blocking_ipc_step;
static unsigned capability_reuse_state;
static unsigned supervisor_probe;
static unsigned extended_state_features_accepted;
static volatile unsigned ordinary_entry_active;
#ifdef LEANOS_ENTRY_HIGH_WATER
static uint64_t entry_stack_high_water_pattern = UINT64_C(0x6c65616e6f735741);
#endif
#ifdef LEANOS_ENTRY_ADVERSARIAL
static unsigned entry_adversarial_step;
#endif
static uint8_t copy_buffer[16];
static unsigned copy_step;
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
/* Exact generated-adapter result retained across the checked peer restore.
   This is an attestation, not a second mutable scheduler/lifecycle projection. */
static uint64_t fault_dispatch_attestation;
#endif
static void finish(uint8_t value);
static __attribute__((noreturn)) void fail(const char *reason);
static void serial_puts(const char *text);
static void serial_putc(char value);
static void serial_u64(uint64_t value);
static void arm_timer(void);
static uint64_t stack_marker(uint64_t stack_pointer);
static void check_cross_bank_negative(void);
static void check_initial_b_frame_negative(void);
#ifdef LEANOS_ENTRY_HIGH_WATER
static void initialize_entry_stack_high_water(void);
static __attribute__((noinline)) void report_entry_stack_high_water(
    const char *path);
#endif

static void record_extended_state_cpuid(void) {
    uint32_t max_leaf, unused_b, unused_c, unused_d;
    __asm__ volatile ("cpuid"
        : "=a"(max_leaf), "=b"(unused_b), "=c"(unused_c), "=d"(unused_d)
        : "a"(0u), "c"(0u));
    if (max_leaf < 1u)
        fail("extended-state-cpuid-leaf");

    uint32_t leaf_a, leaf_b, leaf_c, leaf_d;
    __asm__ volatile ("cpuid"
        : "=a"(leaf_a), "=b"(leaf_b), "=c"(leaf_c), "=d"(leaf_d)
        : "a"(1u), "c"(0u));
    (void)leaf_a;
    (void)leaf_b;
    const uint32_t x87 = (leaf_d >> 0) & 1u;
    const uint32_t mmx = (leaf_d >> 23) & 1u;
    const uint32_t sse = (leaf_d >> 25) & 1u;
    const uint32_t sse2 = (leaf_d >> 26) & 1u;
    const uint32_t xsave = (leaf_c >> 26) & 1u;
    const uint32_t osxsave = (leaf_c >> 27) & 1u;
    const uint32_t avx = (leaf_c >> 28) & 1u;
    if (!x87 || !mmx || !sse || !sse2 || !xsave || !avx || osxsave)
        fail("extended-state-cpuid-contract");
    extended_state_features_accepted = 1;
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    serial_puts("LEANOS/13 EXTENDED-STATE cpuid.1.x87=1 cpuid.1.mmx=1 cpuid.1.sse=1 cpuid.1.sse2=1 cpuid.1.xsave=1 cpuid.1.osxsave=0 cpuid.1.avx=1 cpu=max result=PASS\n");
#endif
}

/* Bind the fast-entry denial recipe to the finite CPU projection modeled by
   LeanOS.PrivilegeEntryControl.  These are trusted CPUID observations, not a
   proof of instruction semantics: the selected QEMU contract must identify as
   AMD, advertise legacy SYSENTER and SYSCALL, and advertise long mode before
   its reviewed MSR denial tuple can authorize a user return. */
static __attribute__((noinline)) void check_fast_entry_cpuid(void) {
    uint32_t max_leaf, vendor_b, vendor_c, vendor_d;
    __asm__ volatile ("cpuid"
        : "=a"(max_leaf), "=b"(vendor_b), "=c"(vendor_c), "=d"(vendor_d)
        : "a"(0u), "c"(0u));
    if (max_leaf < 1u || vendor_b != UINT32_C(0x68747541) ||
        vendor_d != UINT32_C(0x69746e65) ||
        vendor_c != UINT32_C(0x444d4163))
        fail("fast-entry-cpuid-vendor");

    uint32_t leaf_a, leaf_b, leaf_c, leaf_d;
    __asm__ volatile ("cpuid"
        : "=a"(leaf_a), "=b"(leaf_b), "=c"(leaf_c), "=d"(leaf_d)
        : "a"(1u), "c"(0u));
    (void)leaf_a;
    (void)leaf_b;
    (void)leaf_c;
    if (((leaf_d >> 11) & 1u) == 0u)
        fail("fast-entry-cpuid-sysenter");

    uint32_t max_extended;
    __asm__ volatile ("cpuid"
        : "=a"(max_extended), "=b"(leaf_b), "=c"(leaf_c), "=d"(leaf_d)
        : "a"(UINT32_C(0x80000000)), "c"(0u));
    if (max_extended < UINT32_C(0x80000001))
        fail("fast-entry-cpuid-extended-leaf");
    __asm__ volatile ("cpuid"
        : "=a"(leaf_a), "=b"(leaf_b), "=c"(leaf_c), "=d"(leaf_d)
        : "a"(UINT32_C(0x80000001)), "c"(0u));
    if (((leaf_d >> 11) & 1u) == 0u || ((leaf_d >> 29) & 1u) == 0u)
        fail("fast-entry-cpuid-syscall-long-mode");
}

/* Read back every modeled fast-entry MSR after the exception manifest is live
   and before the first CPL3 return.  EFER is compared through the complete
   model mask; all target registers must exactly match the kernel-written
   denial state. */
static void check_fast_entry_control(void) {
    uint64_t state[8];
    read_fast_entry_msrs(state);
    const uint64_t efer_model_mask = (1ull << 0) | (1ull << 8) |
        (1ull << 10) | (1ull << 11);
    const uint64_t efer_denied = (1ull << 8) | (1ull << 10) | (1ull << 11);
    if ((state[0] & efer_model_mask) != efer_denied)
        fail("fast-entry-efer-readback");
    for (unsigned i = 1; i < 8; ++i)
        if (state[i] != 0) fail("fast-entry-target-readback");
}

static uint64_t idt_target(const struct idt_entry *entry) {
    return entry->low | (uint64_t)entry->middle << 16 | (uint64_t)entry->high << 32;
}

/* Trusted machine adapter for LeanOS.InterruptEntry.normalize. `vector` is an
   immediate in the installed stub, never a saved GPR.  This routine owns the
   stateful authorization latch; any rejection reaches the absorbing halt. */
void authorize_interrupt_entry(uint64_t vector, uint64_t has_error,
                               uint64_t frame_address, uint64_t saved_cs) {
    uint64_t flags, cr3;
    __asm__ volatile ("pushfq; pop %0" : "=r"(flags) : : "memory");
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if (ordinary_entry_active) fail("entry-nested");
    ordinary_entry_active = 1;
    if ((flags & ((1ull << 10) | (1ull << 18))) != 0)
        fail("entry-privileged-state");
    uint64_t expected_error, dpl, purpose;
    if (vector == 6) { expected_error = 0; dpl = 0; purpose = 4; }
    else if (vector == 7) { expected_error = 0; dpl = 0; purpose = 5; }
    else if (vector == 14) { expected_error = 1; dpl = 0; purpose = 1; }
    else if (vector == 32) { expected_error = 0; dpl = 0; purpose = 2; }
    else if (vector == 128) { expected_error = 0; dpl = 3; purpose = 3; }
    else fail("entry-vector");
    if (has_error != expected_error) fail("entry-error-shape");
    unsigned user = (saved_cs & 3u) == 3u;
    if (!user && vector != 14) fail("entry-origin");
    if (user && saved_cs != 0x23) fail("entry-user-selector");
    if (!user && (saved_cs & 3u) != 0) fail("entry-kernel-selector");
    uint64_t first = user ? (uint64_t)__entry_stack_start : (uint64_t)boot_stack;
    uint64_t past = user ? (uint64_t)__entry_stack_end :
                           (uint64_t)boot_stack_top;
    uint64_t bytes = user ? 40 : 24;
    if (frame_address < first || frame_address + bytes > past)
        fail("entry-stack-bounds");
    if (user && (frame_address & 15u) != 0) fail("entry-stack-alignment");
    uint64_t descriptor = vector | vector << 8 | has_error << 16;
    uint64_t frame = saved_cs | (uint64_t)user << 8;
    uint64_t context = current_subject | current_subject << 8 | (cr3 >> 12) << 16;
    if (leanos_entry_demo(descriptor, frame, 0x800000, context, 3) == 0)
        fail("entry-model-rejected");
    (void)dpl;
    (void)purpose;
}

void complete_interrupt_entry(void) {
    if (!ordinary_entry_active) fail("entry-complete-unarmed");
    ordinary_entry_active = 0;
}

static void check_entry_manifest(void) {
    struct expected_gate { unsigned vector; void (*target)(void); uint8_t ist, attr; };
    static const struct expected_gate expected[] = {
        { 6, isr6, 0, 0x8e }, { 7, isr7, 0, 0x8e },
        { 8, isr8, 1, 0x8e }, { 13, isr13, 0, 0x8e },
        { 14, isr14, 0, 0x8e }, { 32, isr32, 0, 0x8e },
        { 128, isr80, 0, 0xee }
    };
    for (unsigned vector = 0; vector < 256; ++vector) {
        const struct expected_gate *want = 0;
        for (unsigned i = 0; i < sizeof(expected) / sizeof(expected[0]); ++i)
            if (expected[i].vector == vector) want = &expected[i];
        if (!want) {
            if (idt[vector].attributes & 0x80u) fail("entry-extra-present-gate");
            continue;
        }
        if (idt_target(&idt[vector]) != (uint64_t)want->target ||
            idt[vector].selector != 0x08 || idt[vector].ist != want->ist ||
            idt[vector].attributes != want->attr || idt[vector].zero != 0)
            fail("entry-descriptor-mismatch");
    }
    if (tss.rsp0 != (uint64_t)__entry_stack_end ||
        tss.ist[0] != (uint64_t)__df_ist_stack_end)
        fail("entry-tss-mismatch");
    serial_puts("LEANOS/12 ENTRY-MANIFEST ordinary=5 extended=6,7 auxiliary=2 extra=0 rsp0=entry-stack ist1=df-stack result=PASS\n");
}

#ifdef LEANOS_ENTRY_ADVERSARIAL
uint64_t entry_adversarial_gp_handler(uint64_t error, uint64_t rip,
                                      uint64_t saved_cs) {
    static const uint64_t expected_error[] = { 14u * 8u + 2u, 32u * 8u + 2u };
    if (saved_cs != 0x23 || entry_adversarial_step >= 2 ||
        error != expected_error[entry_adversarial_step])
        fail("entry-adversarial-gp");
    serial_puts("LEANOS/11 ENTRY-ADVERSARIAL attempted-vector=");
    serial_u64(entry_adversarial_step == 0 ? 14 : 32);
    serial_puts(" delivered=13 privileged-handler=unreached result=PASS\n");
    ++entry_adversarial_step;
    return rip + 2;
}
#endif

/* The arrays are emitted only after the linker-resolved Input is accepted by
   LeanOS.BootPageTablePlan.compile. The early assembly constructor remains
   trusted; this guest checker independently decodes and compares its result. */
static uint64_t expected_boot_leaf(unsigned space, uint64_t page) {
#ifdef LEANOS_DF_MAP_GUARD
    uint64_t guard_first = (uint64_t)__df_ist_guard_start / PAGE_BYTES;
    uint64_t guard_last = ((uint64_t)__df_ist_guard_end + PAGE_BYTES - 1u) / PAGE_BYTES;
    if (page >= guard_first && page < guard_last)
        return page * PAGE_BYTES | PTE_PRESENT | PTE_WRITABLE | PTE_NX;
#endif
    return space == 1 ? leanos_boot_plan_a[page] : leanos_boot_plan_b[page];
}

static int decoded_root_matches(unsigned space, uint64_t *root, uint64_t *pdpt,
                                uint64_t *pd, uint64_t *pt, int report_mismatch) {
    if ((root[0] & ~PTE_ACCESSED) != ((uint64_t)pdpt | 7u) ||
        (pdpt[0] & ~PTE_ACCESSED) != ((uint64_t)pd | 7u)) {
        if (report_mismatch) {
            serial_puts("LEANOS/8 PAGING mismatch root="); serial_u64(space);
            serial_puts(" level=ancestor root-expected="); serial_u64((uint64_t)pdpt | 7u);
            serial_puts(" root-actual="); serial_u64(root[0]);
            serial_puts(" pdpt-expected="); serial_u64((uint64_t)pd | 7u);
            serial_puts(" pdpt-actual="); serial_u64(pdpt[0]); serial_putc('\n');
        }
        return 0;
    }
    for (unsigned i = 1; i < 512; ++i)
        if (root[i] != 0 || pdpt[i] != 0) return 0;
    for (unsigned i = 0; i < 512; ++i) {
        uint64_t expected = i < BOOT_PT_COUNT ? (uint64_t)(pt + i * 512u) | 7u : 0;
        if ((pd[i] & ~PTE_ACCESSED) != expected) {
            if (report_mismatch) {
                serial_puts("LEANOS/8 PAGING mismatch root="); serial_u64(space);
                serial_puts(" level=pd index="); serial_u64(i);
                serial_puts(" expected="); serial_u64(expected);
                serial_puts(" actual="); serial_u64(pd[i]); serial_putc('\n');
            }
            return 0;
        }
    }
    for (uint64_t page = 0; page < BOOT_LEAF_COUNT; ++page) {
        uint64_t actual = pt[page];
        uint64_t expected = expected_boot_leaf(space, page);
        if ((actual & ~(PTE_ACCESSED | PTE_DIRTY)) != expected) {
            if (report_mismatch) {
                serial_puts("LEANOS/8 PAGING mismatch root="); serial_u64(space);
                serial_puts(" page="); serial_u64(page);
                serial_puts(" expected="); serial_u64(expected);
                serial_puts(" actual="); serial_u64(actual);
                serial_putc('\n');
            }
            return 0;
        }
    }
    return 1;
}

static void expect_live_mutation_rejected(const char *fixture,
        uint64_t *slot, uint64_t replacement, const char *level, uint64_t page) {
    uint64_t saved = *slot;
    *slot = replacement;
    __asm__ volatile ("" ::: "memory");
    int accepted = decoded_root_matches(2, page_map_level_4_b,
        page_directory_pointer_b, page_directory_b, page_table_b, 0);
    *slot = saved;
    __asm__ volatile ("" ::: "memory");
    if (accepted) fail("pt-live-mutation-accepted");
    serial_puts("LEANOS/8 PAGING fixture="); serial_puts(fixture);
    serial_puts(" root=B level="); serial_puts(level);
    serial_puts(" page="); serial_u64(page);
    serial_puts(" expected="); serial_u64(saved);
    serial_puts(" actual="); serial_u64(replacement);
    serial_puts(" result=REJECTED\n");
}

static uint64_t boot_page(const char *address) {
    return (uint64_t)address / PAGE_BYTES;
}

/* Mutate the actual inactive-B tables, run the same complete walker, and
   restore each slot. These are live-table fixtures: a checker that reads a
   copy, the wrong root, or only a summary cannot reject the full matrix. */
static void check_live_page_table_mutations(void) {
    uint64_t kernel_text = boot_page(__kernel_text_start);
    uint64_t user_text = boot_page(__user_b_text_start);
    uint64_t user_stack = boot_page(__user_b_stack_start);

    expect_live_mutation_rejected("flip-present", &page_table_b[0],
        page_table_b[0] ^ PTE_PRESENT, "pt", 0);
    expect_live_mutation_rejected("flip-user", &page_table_b[user_text],
        page_table_b[user_text] ^ PTE_USER, "pt", user_text);
    expect_live_mutation_rejected("flip-writable", &page_table_b[kernel_text],
        page_table_b[kernel_text] ^ PTE_WRITABLE, "pt", kernel_text);
    expect_live_mutation_rejected("flip-nx", &page_table_b[user_stack],
        page_table_b[user_stack] ^ PTE_NX, "pt", user_stack);
    expect_live_mutation_rejected("wrong-frame", &page_table_b[0],
        page_table_b[0] ^ PAGE_BYTES, "pt", 0);
    expect_live_mutation_rejected("ancestor-pointer", &page_map_level_4_b[0],
        page_map_level_4_b[0] ^ PAGE_BYTES, "pml4", 0);
    expect_live_mutation_rejected("ancestor-flags", &page_directory_pointer_b[0],
        page_directory_pointer_b[0] ^ PTE_USER, "pdpt", 0);

    uint64_t a_text = boot_page(__user_a_text_start);
    uint64_t saved_a = page_table_b[a_text];
    uint64_t saved_b = page_table_b[user_text];
    page_table_b[a_text] = saved_b;
    page_table_b[user_text] = saved_a;
    __asm__ volatile ("" ::: "memory");
    int swapped_accepted = decoded_root_matches(2, page_map_level_4_b,
        page_directory_pointer_b, page_directory_b, page_table_b, 0);
    page_table_b[a_text] = saved_a;
    page_table_b[user_text] = saved_b;
    __asm__ volatile ("" ::: "memory");
    if (swapped_accepted) fail("pt-swapped-leaves-accepted");
    serial_puts("LEANOS/8 PAGING fixture=swapped-user-leaves root=B level=pt page=");
    serial_u64(user_text); serial_puts(" expected="); serial_u64(saved_b);
    serial_puts(" actual="); serial_u64(saved_a);
    serial_puts(" result=REJECTED\n");

#ifndef LEANOS_DF_MAP_GUARD
    uint64_t guard = boot_page(__df_ist_guard_start);
    expect_live_mutation_rejected("extra-mapping", &page_table_b[guard],
        guard * PAGE_BYTES | PTE_PRESENT | PTE_WRITABLE | PTE_NX,
        "pt", guard);
#endif
    uint64_t entry_guard = boot_page(__entry_stack_guard_start);
    expect_live_mutation_rejected("entry-guard-mapping", &page_table_b[entry_guard],
        entry_guard * PAGE_BYTES | PTE_PRESENT | PTE_WRITABLE | PTE_NX,
        "pt", entry_guard);
    expect_live_mutation_rejected("omitted-mapping", &page_table_b[user_text],
        0, "pt", user_text);

    uint64_t selected;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(selected));
    __asm__ volatile ("mov %0, %%cr3" :: "r"((uint64_t)page_map_level_4_b) : "memory");
    uint64_t wrong_selected;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(wrong_selected));
    __asm__ volatile ("mov %0, %%cr3" :: "r"(selected) : "memory");
    if ((wrong_selected & PTE_ADDRESS) == (uint64_t)page_map_level_4_a)
        fail("pt-cr3-fixture-accepted");
    serial_puts("LEANOS/8 PAGING fixture=wrong-cr3 root=A level=cr3 page=0 expected=");
    serial_u64((uint64_t)page_map_level_4_a);
    serial_puts(" actual="); serial_u64(wrong_selected & PTE_ADDRESS);
    serial_puts(" result=REJECTED\n");
}

static void check_boot_page_tables(void) {
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if ((cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_a ||
        &page_map_level_4_a[0] == &page_map_level_4_b[0]) fail("pt-root-a");
    if (!decoded_root_matches(1, page_map_level_4_a, page_directory_pointer_a,
                              page_directory_a, page_table_a, 1)) fail("pt-decode-a");
    serial_puts("LEANOS/8 PAGING root=A selected=1 leaves=4096 policy=manifest result=PASS\n");
    if (!decoded_root_matches(2, page_map_level_4_b, page_directory_pointer_b,
                              page_directory_b, page_table_b, 1)) fail("pt-decode-b");
    serial_puts("LEANOS/8 PAGING root=B selected=0 leaves=4096 policy=manifest result=PASS\n");
    check_live_page_table_mutations();
}

static void check_selected_root_b(void) {
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if ((cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_b) fail("pt-root-b");
    serial_puts("LEANOS/8 PAGING root=B selected=1 result=PASS\n");
}

static void check_selected_root_a(void) {
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if ((cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_a) fail("pt-root-a-resume");
    serial_puts("LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS\n");
}

static void serial_u64(uint64_t value) {
    char digits[21]; unsigned length = 0;
    if (value == 0) { serial_putc('0'); return; }
    while (value != 0) { digits[length++] = (char)('0' + value % 10); value /= 10; }
    while (length != 0) serial_putc(digits[--length]);
}

static unsigned canonical(uint64_t value) {
    uint64_t high = value >> 47;
    return high == 0 || high == 0x1ffffu;
}

#if LEANOS_RETURN_CORRUPTION_MODE != 0
static volatile uint64_t return_corruption_mode = LEANOS_RETURN_CORRUPTION_MODE;

static const char *return_corruption_name(uint64_t mode) {
    switch (mode) {
    case 1: return "kernel-selector";
    case 2: return "wrong-stack-selector";
    case 3: return "noncanonical-rip";
    case 4: return "noncanonical-rsp";
    case 5: return "outside-code";
    case 6: return "outside-stack";
    case 7: return "flags-ac";
    case 8: return "flags-df";
    case 9: return "stale-cr3";
    case 10: return "stale-context";
    case 11: return "post-validation-mutation";
    case 12: return "blocking-context-canary";
    case 13: return "capability-reuse-generation";
#if LEANOS_RETURN_CORRUPTION_MODE == 14
    case 14: return "fast-entry-sce-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 15
    case 15: return "fast-entry-lstar-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 16
    case 16: return "fast-entry-sysenter-eip-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 17
    case 17: return "fast-entry-star-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 18
    case 18: return "fast-entry-cstar-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 19
    case 19: return "fast-entry-sfmask-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 20
    case 20: return "fast-entry-sysenter-cs-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 21
    case 21: return "fast-entry-sysenter-esp-relaxation";
#endif
    default: return "none";
    }
}

/* Controlled negative images corrupt the outgoing frame or one protected
   machine control immediately before the production validator reads it. Each
   image must terminate here, before the first user instruction or iret
   completion can be observed. */
static void inject_return_corruption(uint64_t *saved) {
    uint64_t mode = return_corruption_mode;
    if (mode == 0) return;
    if (mode == 12 && !(current_subject == 2 && blocking_ipc_step == 4)) return;
    if (mode == 13) return;
    serial_puts("LEANOS/9 RETURN fixture=");
    serial_puts(return_corruption_name(mode));
    serial_puts(mode >= 14 && mode <= 21
        ? " stage=machine-control result=INJECTED\n"
        : " stage=outgoing-frame result=INJECTED\n");
    switch (mode) {
    case 1: saved[16] = 0x08; break;
    case 2: saved[19] = 0x10; break;
    case 3: saved[15] = 0x0000800000000000ull; break;
    case 4: saved[18] = 0x0000800000000000ull; break;
    case 5: saved[15] = (uint64_t)user_a_stack; break;
    case 6: saved[18] = (uint64_t)user_a_entry; break;
    case 7: saved[17] |= 1ull << 18; break;
    case 8: saved[17] |= 1ull << 10; break;
    case 9:
        __asm__ volatile ("mov %0, %%cr3" : :
            "r"(current_subject == 1 ? page_map_level_4_b : page_map_level_4_a) :
            "memory");
        break;
    case 10: current_subject = current_subject == 1 ? 2 : 1; break;
    case 11: break;
    case 12: saved[7] ^= 1; break;
#if LEANOS_RETURN_CORRUPTION_MODE == 14
    case 14: {
        uint32_t low, high;
        __asm__ volatile ("rdmsr" : "=a"(low), "=d"(high)
            : "c"(UINT32_C(0xc0000080)));
        low |= 1u;
        __asm__ volatile ("wrmsr" : : "a"(low), "d"(high),
            "c"(UINT32_C(0xc0000080)) : "memory");
        break;
    }
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 15
    case 15: {
        const uint64_t target = (uint64_t)user_a_entry;
        __asm__ volatile ("wrmsr" : : "a"((uint32_t)target),
            "d"((uint32_t)(target >> 32)), "c"(UINT32_C(0xc0000082)) :
            "memory");
        break;
    }
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 16
    case 16: {
        const uint64_t target = (uint64_t)user_a_entry;
        __asm__ volatile ("wrmsr" : : "a"((uint32_t)target),
            "d"((uint32_t)(target >> 32)), "c"(UINT32_C(0x176)) :
            "memory");
        break;
    }
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 17
    case 17:
        __asm__ volatile ("wrmsr" : : "a"(UINT32_C(0x8)), "d"(0),
            "c"(UINT32_C(0xc0000081)) : "memory");
        break;
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 18
    case 18: {
        const uint64_t target = (uint64_t)user_a_entry;
        __asm__ volatile ("wrmsr" : : "a"((uint32_t)target),
            "d"((uint32_t)(target >> 32)), "c"(UINT32_C(0xc0000083)) :
            "memory");
        break;
    }
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 19
    case 19:
        __asm__ volatile ("wrmsr" : : "a"(UINT32_C(0x200)), "d"(0),
            "c"(UINT32_C(0xc0000084)) : "memory");
        break;
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 20
    case 20:
        __asm__ volatile ("wrmsr" : : "a"(UINT32_C(0x8)), "d"(0),
            "c"(UINT32_C(0x174)) : "memory");
        break;
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 21
    case 21: {
        const uint64_t target = (uint64_t)user_a_stack;
        __asm__ volatile ("wrmsr" : : "a"((uint32_t)target),
            "d"((uint32_t)(target >> 32)), "c"(UINT32_C(0x175)) :
            "memory");
        break;
    }
#endif
    default: fail("user-return-fixture-mode");
    }
}
#endif

/* Fixed-width, allocation-free machine adapter for the authoritative return
   policy. `saved` is the complete SAVE register bank followed by RIP, CS,
   RFLAGS, RSP, and SS. Rejection enters the existing absorbing terminal path. */
void validate_user_return(const uint64_t *saved, uint64_t purpose) {
#if LEANOS_RETURN_CORRUPTION_MODE != 0
    inject_return_corruption((uint64_t *)saved);
#endif
    uint64_t rip = saved[15], cs = saved[16], flags = saved[17];
    uint64_t rsp = saved[18], ss = saved[19], cr0, cr3, cr4;
    __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
    const char *code_first, *code_last, *stack_first, *stack_last;
    const uint64_t *expected_cr3;
    if (current_subject == 1) {
        code_first = user_a_entry; code_last = user_a_stack;
        stack_first = user_a_stack; stack_last = user_a_stack_top;
        expected_cr3 = page_map_level_4_a;
    } else if (current_subject == 2) {
        code_first = user_b_entry; code_last = user_b_stack;
        stack_first = user_b_stack; stack_last = user_b_stack_top;
        expected_cr3 = page_map_level_4_b;
    } else fail("user-return-subject");
    if (purpose < 1 || purpose > 3) fail("user-return-purpose");
    if (cs != 0x23 || ss != 0x1b) fail("user-return-selector");
    if (!canonical(rip) || !canonical(rsp)) fail("user-return-noncanonical");
    /* Require IF and architectural bit 1; reject DF, IOPL, NT, RF, VM, AC,
       and every flag outside the deliberately reviewed arithmetic subset. */
    const uint64_t required = (1ull << 1) | (1ull << 9);
    const uint64_t allowed = required | 1ull | (1ull << 2) | (1ull << 4) |
        (1ull << 6) | (1ull << 7) | (1ull << 11);
    if ((flags & required) != required || (flags & ~allowed) != 0)
        fail("user-return-flags");
    if (rip < (uint64_t)code_first || rip >= (uint64_t)code_last)
        fail("user-return-code");
    if (rsp < (uint64_t)stack_first || rsp > (uint64_t)stack_last)
        fail("user-return-stack");
    if (cr3 != (uint64_t)expected_cr3) fail("user-return-cr3");
    const uint64_t required_cr0 = (1ull << 16) | (1ull << 3) |
        (1ull << 2) | (1ull << 1);
    const uint64_t required_cr4 = (1ull << 20) | (1ull << 21);
    const uint64_t forbidden_cr4 = (1ull << 22) | (1ull << 18) |
        (1ull << 10) | (1ull << 9);
    if ((cr0 & required_cr0) != required_cr0 ||
        (cr4 & required_cr4) != required_cr4 ||
        (cr4 & forbidden_cr4) != 0)
        fail("extended-state-denial-peer-controls");
    /* Re-read the complete kernel-produced fast-entry denial tuple at the
       sole outbound gate.  A post-boot relaxation cannot reach iretq. */
    check_fast_entry_control();
    /* Accepted ordinary entries remain armed through handler dispatch and
       context selection.  Clear only in this final validated return gate;
       initial boot dispatch is intentionally unarmed. */
    if (ordinary_entry_active) ordinary_entry_active = 0;
}

static __attribute__((noreturn)) void handoff_fail(const char *reason) {
    serial_puts("LEANOS/7 BOOTALLOC status=FAIL reason="); serial_puts(reason);
    serial_putc('\n'); finish(0x11);
}

static void reserve_byte_range(uint64_t start, uint64_t stop) {
    uint64_t first = start / PAGE_BYTES;
    uint64_t last = (stop + PAGE_BYTES - 1) / PAGE_BYTES;
    if (last > sizeof(boot_frames)) last = sizeof(boot_frames);
    for (uint64_t frame = first; frame < last; ++frame) boot_frames[frame] = 2;
}

/* Bounded, allocation-free Multiboot2 glue. Its correspondence to the Lean
   evidence adapter is tested, but the byte loads themselves remain in the TCB. */
static void boot_allocate(uint32_t magic, uint32_t info_address) {
    if (magic != MULTIBOOT2_RUNTIME_MAGIC) handoff_fail("magic");
    if ((info_address & 7u) != 0 || info_address < PAGE_BYTES ||
        info_address >= BOOT_ACCESSIBLE_LIMIT) handoff_fail("pointer");
    const uint8_t *info = (const uint8_t *)(uint64_t)info_address;
    uint32_t total = *(const uint32_t *)info;
    if (total < 16 || total > MAX_HANDOFF_BYTES || (total & 7u) != 0 ||
        total > BOOT_ACCESSIBLE_LIMIT - info_address) handoff_fail("bounds");

    uint32_t offset = 8, entries = 0, entry_size = 0;
    uint64_t highest_end = 0; unsigned saw_map = 0, saw_end = 0;
    while (offset <= total - 8) {
        const struct mb2_tag *tag = (const struct mb2_tag *)(info + offset);
        if (tag->size < 8 || tag->size > total - offset) handoff_fail("tag-size");
        if (tag->type == 0) {
            if (tag->size != 8) handoff_fail("end-tag");
            saw_end = 1; break;
        }
        if (tag->type == 6) {
            if (saw_map || tag->size < 16) handoff_fail("mmap-shape");
            const struct mb2_mmap_tag *map = (const struct mb2_mmap_tag *)tag;
            if (map->entry_size != sizeof(struct mb2_mmap_entry) ||
                map->entry_version != 0 ||
                (tag->size - 16) % map->entry_size != 0) handoff_fail("mmap-layout");
            entry_size = map->entry_size;
            uint32_t count = (tag->size - 16) / map->entry_size;
            if (count == 0 || count > MAX_MMAP_ENTRIES) handoff_fail("mmap-count");
            for (uint32_t i = 0; i < count; ++i) {
                const struct mb2_mmap_entry *entry = (const struct mb2_mmap_entry *)
                    ((const uint8_t *)map + 16 + i * map->entry_size);
                uint64_t stop;
                if (entry->length == 0 || __builtin_add_overflow(entry->base,
                    entry->length, &stop)) handoff_fail("entry-range");
                uint64_t first, last;
                if (entry->type == 1) {
                    if (stop > highest_end) highest_end = stop;
                    if (entry->base > UINT64_MAX - (PAGE_BYTES - 1))
                        handoff_fail("entry-round");
                    first = (entry->base + PAGE_BYTES - 1) / PAGE_BYTES;
                    last = stop / PAGE_BYTES;
                    if (last > sizeof(boot_frames)) last = sizeof(boot_frames);
                    for (uint64_t frame = first; frame < last; ++frame)
                        if (boot_frames[frame] == 0) boot_frames[frame] = 1;
                } else {
                    first = entry->base / PAGE_BYTES;
                    last = stop >= BOOT_ACCESSIBLE_LIMIT ? sizeof(boot_frames) :
                        (stop + PAGE_BYTES - 1) / PAGE_BYTES;
                    if (last > sizeof(boot_frames)) last = sizeof(boot_frames);
                    for (uint64_t frame = first; frame < last; ++frame)
                        boot_frames[frame] = 2;
                }
            }
            entries = count; saw_map = 1;
        }
        uint32_t advance = (tag->size + 7u) & ~7u;
        if (advance < tag->size || advance > total - offset) handoff_fail("tag-advance");
        offset += advance;
    }
    if (!saw_end || !saw_map) handoff_fail("missing-tag");

    reserve_byte_range(0, 1024u * 1024u);
    reserve_byte_range((uint64_t)__boot_image_start, (uint64_t)__boot_image_end);
    reserve_byte_range(info_address, (uint64_t)info_address + total);
    uint64_t selected = sizeof(boot_frames);
    for (uint64_t frame = 256; frame < sizeof(boot_frames); ++frame)
        if (boot_frames[frame] == 1) { selected = frame; break; }
    if (selected == sizeof(boot_frames)) handoff_fail("no-frame");
    if (leanos_boot_allocation_check(magic, total, entry_size, selected, 15) != 1)
        handoff_fail("model-check");

    volatile uint8_t *frame = (volatile uint8_t *)(selected * PAGE_BYTES);
    for (uint64_t i = 0; i < PAGE_BYTES; ++i) frame[i] = 0;
    for (uint64_t i = 0; i < PAGE_BYTES; ++i)
        if (frame[i] != 0) handoff_fail("scrub");
    published_boot_object = selected + 1; /* publish only after the full scrub */

    serial_puts("LEANOS/7 HANDOFF magic=valid info-bytes="); serial_u64(total);
    serial_puts(" mmap-entries="); serial_u64(entries); serial_puts(" result=PASS\n");
    serial_puts("LEANOS/7 MAP boot-pages="); serial_u64(sizeof(boot_frames));
    serial_puts(" reported-top-mib="); serial_u64(highest_end / (1024u * 1024u));
    serial_puts(" precedence=reserved result=PASS\n");
    serial_puts("LEANOS/7 ALLOC frame="); serial_u64(selected);
    serial_puts(" firmware-usable=1 boot-accessible=1 reserved=0 result=PASS\n");
    serial_puts("LEANOS/7 SCRUB bytes=4096 zero=1 result=PASS\n");
    serial_puts("LEANOS/7 PUBLISH object=1 owner=1 stale-object=denied result=PASS\n");
    serial_puts("LEANOS/7 BOOTALLOC status=PASS\n");
}

enum copy_policy {
    COPY_ALLOWED, COPY_TOO_LONG, COPY_OVERFLOW, COPY_NONCANONICAL,
    COPY_WRONG_SUBJECT, COPY_UNMAPPED, COPY_READ_ONLY, COPY_STALE
};

static enum copy_policy validate_copy(uint64_t subject, unsigned lifetime_current,
                                      uint64_t start, uint64_t length,
                                      unsigned write) {
    uint64_t end;
    if (subject != 1) return COPY_WRONG_SUBJECT;
    if (!lifetime_current) return COPY_STALE;
    if (length > sizeof(copy_buffer)) return COPY_TOO_LONG;
    if (__builtin_add_overflow(start, length, &end)) return COPY_OVERFLOW;
    if (start >= (1ull << 47) || end >= (1ull << 47)) return COPY_NONCANONICAL;
    if (start >= (uint64_t)user_a_entry && start < (uint64_t)user_a_stack) {
        return write ? COPY_READ_ONLY : COPY_UNMAPPED;
    }
    if (start < (uint64_t)user_a_stack || end > (uint64_t)user_a_stack_top)
        return COPY_UNMAPPED;
    return COPY_ALLOWED;
}

static unsigned ac_is_set(void) {
    uint64_t flags;
    __asm__ volatile ("pushfq; pop %0" : "=r"(flags) : : "memory");
    return (unsigned)((flags >> 18) & 1u);
}

static void exercise_copy_policy(void) {
    uint8_t before_buffer[sizeof(copy_buffer)];
    for (unsigned i = 0; i < sizeof(copy_buffer); ++i) {
        copy_buffer[i] = (uint8_t)(0x80u + i);
        before_buffer[i] = copy_buffer[i];
    }
    uint8_t before_user, after_user;
    smap_copy_from(&before_user, user_a_stack, 1);
    if (ac_is_set()) fail("policy-snapshot-ac-set");
    if (validate_copy(1, 1, (uint64_t)user_a_stack, 0, 0) != COPY_ALLOWED ||
        validate_copy(1, 1, (uint64_t)user_a_stack, 16, 0) != COPY_ALLOWED ||
        validate_copy(1, 1, (uint64_t)user_a_stack_top, 1, 0) != COPY_UNMAPPED ||
        validate_copy(1, 1, (uint64_t)user_a_entry, 1, 1) != COPY_READ_ONLY ||
        validate_copy(1, 1, UINT64_MAX - 7, 16, 0) != COPY_OVERFLOW ||
        validate_copy(1, 1, 1ull << 47, 1, 0) != COPY_NONCANONICAL ||
        validate_copy(2, 1, (uint64_t)user_a_stack, 1, 0) != COPY_WRONG_SUBJECT ||
        validate_copy(1, 0, (uint64_t)user_a_stack, 1, 0) != COPY_STALE)
        fail("copy-policy-vectors");
    for (unsigned i = 0; i < sizeof(copy_buffer); ++i)
        if (copy_buffer[i] != before_buffer[i]) fail("copy-reject-buffer-partial");
    smap_copy_from(&after_user, user_a_stack, 1);
    if (ac_is_set()) fail("policy-canary-ac-set");
    if (after_user != before_user) fail("copy-reject-user-partial");
    serial_puts("LEANOS/6 POLICY zero=accept max=accept unmapped=reject readonly=reject overflow=reject noncanonical=reject wrong-subject=reject stale=reject atomic=PASS\n");
}

/* Keep each privileged port instruction in one named final-ELF wrapper.  The
   direct-port site policy inventories these symbols and separately owns the
   PCI configuration wrappers as boot-only DMA-quarantine exceptions. */
static __attribute__((noinline, noipa)) void out8(uint16_t port, uint8_t value) {
    __asm__ volatile ("outb %0, %1" : : "a"(value), "Nd"(port));
}

static __attribute__((noinline, noipa)) uint8_t in8(uint16_t port) {
    uint8_t value;
    __asm__ volatile ("inb %1, %0" : "=a"(value) : "Nd"(port));
    return value;
}

static __attribute__((noinline, noipa)) void out16(uint16_t port, uint16_t value) {
    __asm__ volatile ("outw %0, %1" : : "a"(value), "Nd"(port));
}

static __attribute__((noinline, noipa)) void out32(uint16_t port, uint32_t value) {
    __asm__ volatile ("outl %0, %1" : : "a"(value), "Nd"(port));
}

static __attribute__((noinline, noipa)) uint32_t in32(uint16_t port) {
    uint32_t value;
    __asm__ volatile ("inl %1, %0" : "=a"(value) : "Nd"(port));
    return value;
}

struct pci_manifest_entry {
    uint8_t device, function;
    uint16_t vendor, product;
    uint32_t class_code;
    uint8_t required, multifunction;
};

/* This is the C rendering of DMAQuarantine.q35Manifest for topology version
   0x0008_0002_0002. Configuration mechanism #1 and the behavior of these
   devices remain trusted hardware/QEMU inputs; acceptance is integration
   evidence and is not a refinement theorem for the Lean snapshot. */
static const struct pci_manifest_entry q35_pci_manifest[] = {
    { 0, 0, 0x8086, 0x29c0, 0x060000, 1, 0 },
    { 1, 0, 0x1234, 0x1111, 0x030000, 1, 0 },
    { 3, 0, 0x1af4, 0x1000, 0x020000, 0, 0 },
    { 31, 0, 0x8086, 0x2918, 0x060100, 1, 1 },
    { 31, 2, 0x8086, 0x2922, 0x010601, 1, 1 },
    { 31, 3, 0x8086, 0x2930, 0x0c0500, 1, 1 },
};

static __attribute__((noinline, noipa)) uint32_t pci_config_dword(
        uint8_t device, uint8_t function, uint8_t offset) {
    uint32_t address = UINT32_C(0x80000000) |
        (uint32_t)device << 11 | (uint32_t)function << 8 | (offset & 0xfcu);
    out32(PCI_CONFIG_ADDRESS, address);
    return in32(PCI_CONFIG_DATA);
}

static __attribute__((noinline, noipa)) void pci_config_command(
        uint8_t device, uint8_t function, uint16_t command) {
    uint32_t address = UINT32_C(0x80000000) |
        (uint32_t)device << 11 | (uint32_t)function << 8 | 0x04u;
    out32(PCI_CONFIG_ADDRESS, address);
    out16(PCI_CONFIG_DATA, command);
}

static const struct pci_manifest_entry *q35_manifest_entry(
        uint8_t device, uint8_t function, unsigned *index) {
    for (unsigned i = 0;
         i < sizeof(q35_pci_manifest) / sizeof(q35_pci_manifest[0]); ++i) {
        if (q35_pci_manifest[i].device == device &&
            q35_pci_manifest[i].function == function) {
            *index = i;
            return &q35_pci_manifest[i];
        }
    }
    return 0;
}

/* Exhaustively account for all 256 functions on the manifest's finite bus,
   clear bus mastering on every present function, and independently read back
   each complete modeled Command word. This runs after firmware and before the
   first CPL3 return. Missing required functions and extra or changed readable
   functions are fatal; an all-ones vendor read is treated as absence, including
   for the optional NIC slot, under the documented configuration-read assumption. */
static __attribute__((noinline, noipa)) void quarantine_q35_pci_dma(void) {
    unsigned seen = 0, present = 0, writes = 0, readbacks = 0;
    unsigned initially_bus_mastering = 0;
    unsigned initial_bus_master_mask = 0;
    for (unsigned device = 0; device < 32; ++device) {
        for (unsigned function = 0; function < 8; ++function) {
            uint32_t identity = pci_config_dword(device, function, 0x00);
            uint16_t vendor = (uint16_t)identity;
            if (vendor == UINT16_MAX) continue;

            unsigned index = 0;
            const struct pci_manifest_entry *entry =
                q35_manifest_entry(device, function, &index);
            if (!entry || (seen & (1u << index))) fail("dma-inventory");

            uint16_t product = (uint16_t)(identity >> 16);
            uint32_t class_code = pci_config_dword(device, function, 0x08) >> 8;
            uint8_t header = (uint8_t)(pci_config_dword(
                device, function, 0x0c) >> 16);
            if (vendor != entry->vendor || product != entry->product ||
                class_code != entry->class_code ||
                ((header >> 7) & 1u) != entry->multifunction)
                fail("dma-identity");

            uint16_t command = (uint16_t)pci_config_dword(
                device, function, 0x04);
            if ((command & PCI_COMMAND_BUS_MASTER) != 0) {
                ++initially_bus_mastering;
                initial_bus_master_mask |= 1u << index;
            }
            uint16_t expected_command =
                (uint16_t)(command & ~PCI_COMMAND_BUS_MASTER);
            pci_config_command(device, function, expected_command);
            ++writes;
            command = (uint16_t)pci_config_dword(device, function, 0x04);
            ++readbacks;
            if (command != expected_command ||
                (command & PCI_COMMAND_BUS_MASTER) != 0 ||
                (command & ~PCI_COMMAND_MODEL_MASK) != 0)
                fail("dma-command-readback");
            seen |= 1u << index;
            ++present;
        }
    }

    unsigned optional_absent = 0;
    for (unsigned i = 0;
         i < sizeof(q35_pci_manifest) / sizeof(q35_pci_manifest[0]); ++i) {
        if (seen & (1u << i)) continue;
        if (q35_pci_manifest[i].required) fail("dma-required-missing");
        ++optional_absent;
    }
    if (present == 0) fail("dma-empty-inventory");
    if (present != 5 || optional_absent != 1 || writes != present ||
        readbacks != present)
        fail("dma-q35-nic-none");
    serial_puts("LEANOS/15 DMA snapshot=1 topology=000800020002 bus=0 scanned=256 present=5 optional-absent=1 writes=5 readbacks=5 initial-bus-masters=");
    serial_u64(initially_bus_mastering);
    serial_puts(" initial-bus-master-mask=");
    serial_u64(initial_bus_master_mask);
    serial_puts(" bus-master=disabled readback=exact stage=pre-cpl3 result=PASS\n");
}

static void serial_init(void) {
    out8(COM1 + 1, 0x00);
    out8(COM1 + 3, 0x80);
    out8(COM1 + 0, 0x03);
    out8(COM1 + 1, 0x00);
    out8(COM1 + 3, 0x03);
    out8(COM1 + 2, 0xc7);
    out8(COM1 + 4, 0x0b);
}

static void serial_putc(char value) {
    while ((in8(COM1 + 5) & 0x20u) == 0) {
    }
    out8(COM1, (uint8_t)value);
}

static void serial_puts(const char *text) {
    while (*text != '\0') {
        serial_putc(*text++);
    }
}

static void replay_oracle(void) {
    for (unsigned i = 0; i < ORACLE_VECTOR_COUNT; ++i) {
        const struct oracle_vector *v = &oracle_vectors[i];
        uint64_t got = v->adapter == 0
            ? leanos_boot_transition(v->words[0], v->words[1])
            : v->adapter == 1
                ? leanos_syscall_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                : v->adapter == 2
                    ? leanos_ipc_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                : v->adapter == 3
                    ? leanos_preemption_demo(v->words[0], v->words[1], v->words[2], v->words[3])
                : v->adapter == 4
                    ? leanos_resumable_preemption_demo(v->words[0], v->words[1], v->words[2],
                        v->words[3], v->words[4])
                : v->adapter == 5
                        ? leanos_boot_allocation_check(v->words[0], v->words[1], v->words[2],
                            v->words[3], v->words[4])
                        : v->adapter == 6
                            ? leanos_user_return_demo(v->words[0], v->words[1], v->words[2],
                                v->words[3], v->words[4])
                            : v->adapter == 7
                                ? leanos_blocking_ipc_demo(v->words[0], v->words[1], v->words[2],
                                    v->words[3], v->words[4])
                                : v->adapter == 8
                                    ? leanos_capability_reuse_demo(v->words[0], v->words[1],
                                        v->words[2], v->words[3], v->words[4])
                                    : v->adapter == 9
                                        ? leanos_entry_demo(v->words[0], v->words[1], v->words[2],
                                            v->words[3], v->words[4])
                                        : v->adapter == 10
                                            ? leanos_extended_state_denial_demo(v->words[0],
                                                v->words[1], v->words[2], v->words[3],
                                                v->words[4], v->words[5])
                                            : v->adapter == 11
                                                ? leanos_privilege_entry_control_demo(v->words[0],
                                                v->words[1], v->words[2], v->words[3],
                                                v->words[4], v->words[5])
                                                : v->adapter == 12
                                                    ? leanos_fault_dispatch_demo(v->words[0],
                                                    v->words[1], v->words[2], v->words[3],
                                                    v->words[4], v->words[5])
                                                    : leanos_direct_port_io_demo(v->words[0],
                                                    v->words[1], v->words[2], v->words[3],
                                                    v->words[4], v->words[5]);
        serial_puts("LEANOS/3 ORACLE id="); serial_puts(v->id);
        if (got != v->expected) {
            serial_puts(" result=FAIL\nLEANOS/3 FINAL status=FAIL reason=oracle\n");
            finish(0x11);
        }
        serial_puts(" result=PASS\n");
    }
}

static __attribute__((noreturn)) void finish(uint8_t value) {
    out8(DEBUG_EXIT, value);
    for (;;) {
        __asm__ volatile ("cli; hlt");
    }
}

static __attribute__((noreturn)) void fail(const char *reason) {
    serial_puts("LEANOS/3 FINAL status=FAIL reason=");
    serial_puts(reason);
    serial_putc('\n');
    finish(0x11);
}

static void set_gate(unsigned vector, void (*handler)(void), uint8_t ist,
                     uint8_t attributes) {
    uint64_t address = (uint64_t)handler;
    idt[vector] = (struct idt_entry){ (uint16_t)address, 0x08, ist, attributes,
        (uint16_t)(address >> 16), (uint32_t)(address >> 32), 0 };
}

static void privilege_init(void) {
    uint64_t base = (uint64_t)&tss;
    uint64_t limit = sizeof(tss) - 1;
    gdt64[5] = (limit & 0xffffu) | ((base & 0xffffffu) << 16) |
        (0x89ull << 40) | (((limit >> 16) & 0xfu) << 48) |
        (((base >> 24) & 0xffu) << 56);
    gdt64[6] = base >> 32;
    tss.rsp0 = (uint64_t)__entry_stack_end;
    tss.ist[0] = (uint64_t)__df_ist_stack_end;
    tss.iomap = sizeof(tss);
#ifdef LEANOS_ENTRY_HIGH_WATER
    initialize_entry_stack_high_water();
#endif
    *(uint64_t *)__df_ist_stack_start = 0xd0b1efa17badc0deull;
    *(uint64_t *)((uint64_t)__df_ist_stack_end - 128u) =
        0x15a1c0decafef00dull;
    set_gate(8, isr8, 1, 0x8e);
    set_gate(6, isr6, 0, 0x8e);
    set_gate(7, isr7, 0, 0x8e);
    set_gate(13, isr13, 0, 0x8e);
    set_gate(14, isr14, 0, 0x8e);
    set_gate(32, isr32, 0, 0x8e);
    set_gate(0x80, isr80, 0, 0xee);
    check_entry_manifest();
    /* Firmware may leave legacy IRQ lines unmasked.  Keep asynchronous input
       outside the ordinary-entry protocol until the preemption scenario has
       remapped the PIC and deliberately armed its bounded timer. */
    out8(0x21, 0xff);
    out8(0xa1, 0xff);
    struct descriptor idtr = { sizeof(idt) - 1, (uint64_t)idt };
    __asm__ volatile ("lidt %0" : : "m"(idtr));
    load_tss();
}

#ifdef LEANOS_ENTRY_HIGH_WATER
/* This painted-stack scan is deliberately diagnostic rather than
   authoritative.  The final-ELF/compiler budget gate remains the acceptance
   criterion; normal QEMU runs retain this bounded observation as evidence
   that the exercised path stayed above the declared safety margin. */
static void initialize_entry_stack_high_water(void) {
    volatile uint64_t *cursor = (volatile uint64_t *)__entry_stack_start;
    volatile uint64_t *past = (volatile uint64_t *)__entry_stack_end;
    while (cursor < past) *cursor++ = entry_stack_high_water_pattern;
}

static __attribute__((noinline)) void report_entry_stack_high_water(
    const char *path) {
    volatile uint64_t *cursor = (volatile uint64_t *)__entry_stack_start;
    volatile uint64_t *past = (volatile uint64_t *)__entry_stack_end;
    while (cursor < past && *cursor == entry_stack_high_water_pattern) ++cursor;
    uint64_t used = (uint64_t)__entry_stack_end - (uint64_t)cursor;
    uint64_t usable = (uint64_t)__entry_stack_end -
        (uint64_t)__entry_stack_start;
    if (used < 176 || used > usable || usable - used < 4096)
        fail("entry-stack-high-water");
    serial_puts("LEANOS/11 ENTRY-HIGH-WATER path="); serial_puts(path);
    serial_puts(" observed-bytes="); serial_u64(used);
    serial_puts(" usable-bytes="); serial_u64(usable);
    serial_puts(" margin-bytes="); serial_u64(usable - used);
    serial_puts(" authority=diagnostic result=PASS\n");
}
#endif
/* Vector 6/7 traverse the shared normalized entry boundary and bounded
   generated cleanup/peer decision.  The dedicated denial scenario publishes
   the selected fresh peer through the sole validated user-return path. */
uint64_t extended_state_denial_handler(uint64_t vector, uint64_t saved_cs,
                                       uint64_t saved_rip) {
    if ((vector != 6 && vector != 7) || saved_cs != 0x23)
        fail("extended-state-denial-binding");
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    if (saved_rip != (uint64_t)user_a_extended_state_probe)
        fail("extended-state-denial-probe-rip");
#else
    (void)saved_rip;
#endif
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    uint64_t expected_cr3 = current_subject == 1 ? (uint64_t)page_map_level_4_a :
        current_subject == 2 ? (uint64_t)page_map_level_4_b : 0;
    if (expected_cr3 == 0 || cr3 != expected_cr3)
        fail("extended-state-denial-binding");
    uint64_t cr0, cr4;
    __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
    const uint64_t required_cr0 = (1ull << 3) | (1ull << 2) | (1ull << 1);
    const uint64_t forbidden_cr4 =
        (1ull << 22) | (1ull << 18) | (1ull << 10) | (1ull << 9);
    uint64_t policy = extended_state_features_accepted &&
        (cr0 & required_cr0) == required_cr0 && (cr4 & forbidden_cr4) == 0;
    const uint64_t initial_live = (1ull << 1) | (1ull << 2);
    if (extended_state_authority.live != initial_live ||
        extended_state_authority.ready != (1ull << 2) ||
        extended_state_authority.current != current_subject ||
        extended_state_authority.contexts != (1ull << 2) ||
        extended_state_authority.active != current_subject)
        fail("extended-state-denial-authority-prestate");
    uint64_t peer;
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    if (extended_state_probe_class >= 5) {
        if (vector != 6 || !policy)
            fail("fast-entry-denial-vector");
        uint64_t event = extended_state_probe_class == 5 ? 2 : 3;
        uint64_t transition = leanos_privilege_entry_control_demo(
            1, 0, event, vector, extended_state_authority.current,
            extended_state_authority.active);
        if (transition != 0xd001)
            fail("fast-entry-denial-model");
        peer = 2;
    } else {
#endif
        uint64_t mode = vector == 6 ? 6 : 0;
        uint64_t transition = leanos_extended_state_denial_demo(policy, mode, vector,
            extended_state_authority.current, extended_state_authority.active,
            extended_state_authority.current);
        if ((transition & 0xffffffffffffff00ull) != 0x3f00000000000100ull)
            fail("extended-state-denial-model");
        peer = transition & 0xffu;
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    }
#endif
    if (peer != 2 || (extended_state_authority.ready & (1ull << peer)) == 0 ||
        (extended_state_authority.contexts & (1ull << peer)) == 0)
        fail("extended-state-denial-authority-selection");
    extended_state_authority.live &= ~(1ull << current_subject);
    extended_state_authority.ready &= ~((1ull << current_subject) | (1ull << peer));
    extended_state_authority.contexts &= ~((1ull << current_subject) | (1ull << peer));
    extended_state_authority.current = peer;
    extended_state_authority.active = peer;
    if (extended_state_authority.live != (1ull << peer) ||
        extended_state_authority.ready != 0 || extended_state_authority.contexts != 0 ||
        extended_state_authority.current != peer || extended_state_authority.active != peer)
        fail("extended-state-denial-authority-poststate");
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    if (current_subject != 1 || peer != 2)
        fail("extended-state-denial-scenario-binding");
    if (extended_state_probe_class > 6)
        fail("extended-state-denial-probe-class");
    uint64_t expected_vector = extended_state_probe_class >= 2 ? 6 : 7;
    if (vector != expected_vector)
        fail("extended-state-denial-probe-vector");
    current_subject = peer;
    extended_state_selected_cr3 = (uint64_t)page_map_level_4_b;
    serial_puts(extended_state_probe_class >= 5
        ? "LEANOS/14 FAST-ENTRY event=deny subject=1 vector="
        : "LEANOS/13 EXTENDED-STATE event=deny subject=1 vector=");
    serial_u64(vector);
    serial_puts(" instruction=");
    serial_puts(extended_state_probe_class == 0 ? "x87" :
        extended_state_probe_class == 1 ? "mmx" :
        extended_state_probe_class == 2 ? "sse" :
        extended_state_probe_class == 3 ? "sse2" :
        extended_state_probe_class == 4 ? "avx" :
        extended_state_probe_class == 5 ? "syscall" : "sysenter");
    serial_puts(extended_state_probe_class >= 5
        ? " alternate-target=unreached cleanup=complete peer=2\n"
        : " bank-write=prevented cleanup=complete peer=2\n");
    return (uint64_t)initial_context_b;
#else
    fail("extended-state-denial-dispatch-unpublished");
#endif
}

uint64_t syscall_handler(uint64_t number, uint64_t arg0, uint64_t arg1,
                         uint64_t arg2, uint64_t saved_cs,
                         uint64_t saved_flags) {
    if ((saved_cs & 3u) != 3u) {
        fail("not-ring3");
    }
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
    if (number == 14 && current_subject == 2) {
        check_selected_root_b();
        if (arg0 != UINT64_C(0xb2b2cafe51a7e55e) || arg1 != 0x030201 ||
            arg2 != 0x51a7 ||
            fault_dispatch_attestation != UINT64_C(0x00000000ff020202))
            fail("fault-peer-state");
        serial_puts("LEANOS/14 PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS\n");
        serial_puts("LEANOS/14 FINAL status=PASS faulting=terminated survivor=2 kernel-origin=fail-stop\n");
        finish(0x10);
    }
#endif
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    if (current_subject == 2 && number == 13) {
#ifdef LEANOS_EXTENDED_STATE_PEER_PKE_FIXTURE
        serial_puts("LEANOS/13 EXTENDED-STATE event=peer-cpl3-entry subject=2\n");
#endif
        uint64_t cr0, cr4, cr3;
        __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
        __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
        __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
        const uint64_t required = (1ull << 3) | (1ull << 2) | (1ull << 1);
        const uint64_t forbidden_peer_cr4 = (1ull << 22) | (1ull << 18) |
            (1ull << 10) | (1ull << 9);
        if ((cr0 & required) != required || (cr4 & forbidden_peer_cr4) != 0 ||
            cr3 != (uint64_t)page_map_level_4_b)
            fail("extended-state-denial-peer-controls");
        serial_puts(extended_state_probe_class >= 5
            ? "LEANOS/14 FAST-ENTRY event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved\n"
            : "LEANOS/13 EXTENDED-STATE event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved\n");
        serial_puts(extended_state_probe_class >= 5
            ? "LEANOS/14 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1 alternate-target=0\n"
            : "LEANOS/13 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1\n");
        finish(0x10);
    }
#endif
    if (capability_reuse_state == 0 && current_subject == 2 && number == 10) {
        uint64_t got = leanos_capability_reuse_demo(
            capability_reuse_state, 1, arg0, arg1, arg2);
        uint64_t event = got & 0xffu;
        uint64_t next_state = (got >> 8) & 0xffu;
        uint64_t evidence = (got >> 16) & 0xffu;
        uint64_t slot = (got >> 24) & 0xffffu;
        uint64_t generation = (got >> 40) & 0xffffu;
        uint64_t endpoint = (got >> 56) & 0xffu;
        uint64_t checked_word = generation * 65536u + slot;
        if (got != oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_INITIAL].expected ||
            event != 1 || next_state != 1 || evidence != 11 || checked_word != arg0)
            fail("capability-reuse-initial");
        capability_reuse_state = next_state;
        serial_puts("LEANOS/9 CAPREUSE event=initial subject="); serial_u64(current_subject);
        serial_puts(" handle="); serial_u64(checked_word);
        serial_puts(" endpoint="); serial_u64(endpoint);
        serial_puts(" accepted="); serial_u64(evidence & 1u); serial_putc('\n');

        got = leanos_capability_reuse_demo(
            capability_reuse_state, 1, arg0, arg1, arg2);
        event = got & 0xffu;
        next_state = (got >> 8) & 0xffu;
        evidence = (got >> 16) & 0xffu;
        slot = (got >> 24) & 0xffffu;
        uint64_t fresh_generation = (got >> 40) & 0xffffu;
        endpoint = (got >> 56) & 0xffu;
        uint64_t fresh_word = fresh_generation * 65536u + slot;
        if (got != oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_CLEARED_SLOT].expected ||
            event != 2 || next_state != 2 || evidence != 15)
            fail("capability-reuse-replace");
        capability_reuse_state = next_state;
        serial_puts("LEANOS/9 CAPREUSE event=clear slot="); serial_u64(checked_word & 0xffffu);
        serial_puts(" old-generation="); serial_u64(checked_word / 65536u);
        serial_puts(" result="); serial_puts((evidence & 1u) ? "PASS\n" : "FAIL\n");
        serial_puts("LEANOS/9 CAPREUSE event=install slot="); serial_u64(slot);
        serial_puts(" generation="); serial_u64(fresh_generation);
        serial_puts(" endpoint="); serial_u64(endpoint);
        serial_puts(" result="); serial_puts((evidence & 14u) == 14u ? "PASS\n" : "FAIL\n");
        return fresh_word;
    }
    if (capability_reuse_state == 2 && current_subject == 2 && number == 11) {
        uint64_t checked_word = arg0;
#if LEANOS_RETURN_CORRUPTION_MODE == 13
        serial_puts("LEANOS/9 CAPREUSE fixture=capability-reuse-generation stage=word-boundary result=INJECTED\n");
        /* A valid slot with generation 2 in the low 32 bits. Any accidental
         * 48-to-32-bit truncation aliases the live stale handle and would
         * accept; the full-width adapter must reject it. */
        checked_word = UINT64_C(0x100000002) * UINT64_C(65536) + (arg0 & 0xffffu);
#endif
        uint64_t got = leanos_capability_reuse_demo(
            capability_reuse_state, 1, checked_word, arg1, arg2);
        uint64_t event = got & 0xffu;
        uint64_t next_state = (got >> 8) & 0xffu;
        uint64_t evidence = (got >> 16) & 0xffu;
        uint64_t slot = (got >> 24) & 0xffffu;
        uint64_t generation = (got >> 40) & 0xffffu;
        uint64_t endpoint = (got >> 56) & 0xffu;
        uint64_t returned_word = generation * 65536u + slot;
        if (got != oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_STALE_GENERATION].expected ||
            event != 3 || next_state != 3 || evidence != 8 || returned_word != checked_word)
            fail("capability-reuse-generation");
        capability_reuse_state = next_state;
        serial_puts("LEANOS/9 CAPREUSE event=stale-replay subject="); serial_u64(current_subject);
        serial_puts(" handle="); serial_u64(returned_word);
        serial_puts(" rejected="); serial_u64((evidence & 1u) == 0); serial_putc('\n');
        serial_puts("LEANOS/9 CAPREUSE event=unchanged endpoint="); serial_u64(endpoint);
        serial_puts(" mailbox="); serial_puts((evidence & 8u) ? "empty" : "changed");
        serial_puts(" result="); serial_puts((evidence & 8u) ? "PASS\n" : "FAIL\n");
        return 0;
    }
    if (capability_reuse_state == 3 && current_subject == 2 && number == 12) {
        uint64_t got = leanos_capability_reuse_demo(
            capability_reuse_state, 1, arg0, arg1, arg2);
        uint64_t event = got & 0xffu;
        uint64_t next_state = (got >> 8) & 0xffu;
        uint64_t evidence = (got >> 16) & 0xffu;
        uint64_t slot = (got >> 24) & 0xffffu;
        uint64_t generation = (got >> 40) & 0xffffu;
        uint64_t endpoint = (got >> 56) & 0xffu;
        uint64_t returned_word = generation * 65536u + slot;
        if (got != oracle_vectors[ORACLE_INDEX_CAPABILITY_REUSE_FRESH_GENERATION].expected ||
            event != 4 || next_state != 4 || evidence != 5 || returned_word != arg0)
            fail("capability-reuse-fresh");
        capability_reuse_state = next_state;
        serial_puts("LEANOS/9 CAPREUSE event=fresh subject="); serial_u64(current_subject);
        serial_puts(" handle="); serial_u64(returned_word);
        serial_puts(" endpoint="); serial_u64(endpoint);
        serial_puts(" accepted="); serial_u64(evidence & 1u); serial_putc('\n');
        serial_puts("LEANOS/9 CAPREUSE status=PASS stale-effects=");
        serial_u64((evidence & 8u) != 0);
        serial_puts(" fresh-effects="); serial_u64((evidence & 4u) != 0); serial_putc('\n');
        return evidence & 1u;
    }
    if (blocking_ipc_step == 0 && current_subject == 2 && number == 7) {
        if (capability_reuse_state != 4) fail("capability-reuse-missing");
        uint64_t got = leanos_blocking_ipc_demo(0, 1, 2, 0x4c45414e, 0x4f53);
        if (got != oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_BLOCK_B].expected)
            fail("blocking-ipc-model-block");
        blocking_ipc_step = 1;
        current_subject = 1;
        serial_puts("LEANOS/10 IPC event=block subject=2 endpoint=10 empty=1 runnable=0 result=PASS\n");
        return 0xbeef;
    }
    if (current_subject == 1 && number == 4) {
        if ((saved_flags & (1u << 10)) == 0) fail("copy-df-not-set");
        uint64_t start = arg1;
        if (validate_copy(current_subject, 1, start, arg2, arg0 == 1) != COPY_ALLOWED)
            fail("copy-policy");
        if (arg0 == 0 && copy_step == 0) {
            smap_copy_from(copy_buffer, (const void *)start, arg2);
            if (ac_is_set()) fail("copy-in-ac-set");
            if (arg2 != 4 || copy_buffer[0] != 0x5a || copy_buffer[1] != 0xa5 ||
                copy_buffer[2] != 0x3c || copy_buffer[3] != 0xc3) fail("copy-in-data");
            copy_step = 1;
            serial_puts("LEANOS/6 COPY direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS\n");
            return 0;
        }
        if (arg0 == 1 && copy_step == 1) {
            smap_copy_to((void *)start, copy_buffer, arg2);
            if (ac_is_set()) fail("copy-out-ac-set");
            copy_step = 2;
            serial_puts("LEANOS/6 COPY direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS\n");
            return 0;
        }
        fail("copy-sequence");
    }
    if (preemption_step == 0 && current_subject == 1 && number == 1) {
        if (copy_step != 2) fail("copy-missing");
        serial_puts("LEANOS/5 ENTRY subject=1 address-space=1 cpl=3 yielding=0\n");
        preemption_step = 1;
        return 0;
    }
    if (preemption_step == 3 && current_subject == 2 && number == 2) {
        serial_puts("LEANOS/5 SYSCALL subject=2 caller=2 address-space=2 authorized=1 canaries=preserved\n");
        preemption_step = 4;
        arm_timer();
        return 0;
    }
    if (current_subject == 1 && number == 6) {
        if (preemption_step == 1) return 0;
        if (preemption_step == 6) return 1;
        fail("resume-probe-state");
    }
    if (blocking_ipc_step == 2 && current_subject == 1 && number == 8) {
        uint64_t sent = leanos_blocking_ipc_demo(1, 2, 1, arg0, arg1);
        uint64_t dispatched = leanos_blocking_ipc_demo(2, 3, 1, arg0, arg1);
        if (sent != oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_SEND_WAKE_B].expected ||
            dispatched != oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_DISPATCH_B].expected)
            fail("blocking-ipc-model-send");
        blocking_ipc_step = 3;
        current_subject = 2;
        serial_puts("LEANOS/10 IPC event=send sender=1 endpoint=10 payload0=1279607118 payload1=20307 accepted=1\n");
        serial_puts("LEANOS/10 IPC event=wake subject=2 ready-insertions=1 reserved=1 result=PASS\n");
        return 0xcafe;
    }
    if (blocking_ipc_step == 4 && current_subject == 2 && number == 9) {
        uint64_t got = leanos_blocking_ipc_demo(3, 4, 2, arg0, arg1);
        if (got != oracle_vectors[ORACLE_INDEX_BLOCKING_IPC_DELIVER_B].expected || arg2 != 1)
            fail("blocking-ipc-model-delivery");
        serial_puts("LEANOS/10 IPC event=deliver receiver=2 endpoint=10 sender=1 payload0=1279607118 payload1=20307 exact=1 canaries=preserved\n");
#ifdef LEANOS_ENTRY_HIGH_WATER
        report_entry_stack_high_water("syscall");
#endif
        serial_puts("LEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1\n");
        finish(0x10);
    }
    if (preemption_step == 6 && current_subject == 1 && number == 5) {
        if (timer_accepted != 2 || saved_context_a[3] != 0xa11ca11ca11ca11cull ||
            saved_context_a[2] != 0xa22da22da22da22dull ||
            saved_context_b[3] != 0xc0dec0dec0dec0deull ||
            saved_context_b[2] != 0x51a7e51a7e51a7e5ull ||
            saved_context_a[15] != saved_context_a_original_rip ||
            saved_context_a[17] != saved_context_a_original_flags ||
            saved_context_a[18] != saved_context_a_original_rsp ||
            saved_context_b[15] != saved_context_b_original_rip ||
            saved_context_b[17] != saved_context_b_original_flags ||
            saved_context_b[18] != saved_context_b_original_rsp ||
            saved_context_a[16] != 0x23 || saved_context_a[19] != 0x1b ||
            saved_context_b[16] != 0x23 || saved_context_b[19] != 0x1b)
            fail("saved-context");
#ifdef LEANOS_ENTRY_HIGH_WATER
        report_entry_stack_high_water("timer-context-switch");
#endif
        serial_puts("LEANOS/5 RESUME subject=1 caller=1 address-space=1 frame=original canaries=preserved contexts=separate\n");
        serial_puts("LEANOS/5 FINAL status=PASS ticks=2\n");
        finish(0x10);
    }
    if (number == 3) fail("register-canary");
    fail("ipc-sequence");
}

uint64_t timer_handler(uint64_t saved_cs) {
    /* Mask IRQ0 before acknowledging it: duplicate ticks cannot enter the
       protocol.  The PIC/PIT bridge is trusted and documented in ADR 0005. */
    out8(0x21, 0xff);
    out8(0x20, 0x20);
    uint64_t queued;
    if ((saved_cs & 3u) != 3u) fail("timer-origin");
    if (current_subject == 1 && preemption_step == 1 && timer_accepted == 0)
        queued = 2;
    else if (current_subject == 2 && preemption_step == 4 && timer_accepted == 1)
        queued = 1;
    else fail("timer-context");
    uint64_t old_subject = current_subject;
    uint64_t modeled = leanos_preemption_demo(32, current_subject, queued, 1);
    uint64_t next_subject = modeled & 0xffffffffu;
    uint64_t next_address_space = modeled >> 32;
    if (next_subject != queued || next_address_space != queued) fail("modeled-tick");
    ++timer_accepted;
    serial_puts(timer_accepted == 1
        ? "LEANOS/5 TIMER vector=32 source=pit mode=bounded-one-shot sequence=1 origin=cpl3 accepted=1\n"
        : "LEANOS/5 TIMER vector=32 source=pit mode=bounded-one-shot sequence=2 origin=cpl3 accepted=1\n");
    serial_puts(old_subject == 1
        ? "LEANOS/5 CONTEXT old-subject=1 old-address-space=1 new-subject=2 new-address-space=2 policy=round-robin\n"
        : "LEANOS/5 CONTEXT old-subject=2 old-address-space=2 new-subject=1 new-address-space=1 policy=round-robin\n");
    current_subject = next_subject;
    preemption_step = next_subject == 2 ? 2 : 5;
    return next_subject;
}

static uint64_t stack_marker(uint64_t stack_pointer) {
    if (stack_pointer >= (uint64_t)user_a_stack &&
        stack_pointer <= (uint64_t)user_a_stack_top) return 1;
    if (stack_pointer >= (uint64_t)user_b_stack &&
        stack_pointer <= (uint64_t)user_b_stack_top) return 2;
    fail("context-stack");
}

static uint64_t context_descriptor(uint64_t owner, uint64_t stack_pointer) {
    if (owner != 1 && owner != 2) fail("context-owner");
    return owner | (stack_marker(stack_pointer) << 8);
}

static void check_original_frame(const uint64_t *frame, uint64_t original_rip,
                                 uint64_t original_flags, uint64_t original_rsp,
                                 uint64_t owner) {
    if (frame[15] != original_rip || frame[17] != original_flags ||
        frame[18] != original_rsp ||
        stack_marker(original_rsp) != owner)
        fail("context-frame-changed");
}

static int initial_b_frame_valid(const volatile uint64_t *frame) {
    return frame[15] == (uint64_t)user_b_entry && frame[16] == 0x23 &&
        frame[17] == 0x202 && frame[18] == (uint64_t)user_b_stack_top &&
        frame[19] == 0x1b;
}

static void check_initial_b_frame(const volatile uint64_t *frame) {
    if (!initial_b_frame_valid(frame)) fail("initial-context-frame");
}

static void check_resumable_witness(uint64_t leg, const uint64_t *target,
                                    const uint64_t *saved, uint64_t target_owner,
                                    uint64_t saved_owner, unsigned vector_index) {
    uint64_t got = leanos_resumable_preemption_demo(leg,
        context_descriptor(target_owner, target[18]),
        context_descriptor(saved_owner, saved[18]),
        target[3] & 0xffu, saved[3] & 0xffu);
    if (got != oracle_vectors[vector_index].expected) fail("modeled-restore");
}

void switch_complete(uint64_t *target, uint64_t target_owner, uint64_t saved_owner) {
    if (current_subject == 1 && blocking_ipc_step == 1) {
        check_selected_root_a();
        if (target_owner != 1 || saved_owner != 2) fail("blocking-ipc-switch-a-owner");
        check_original_frame(saved_context_b, saved_context_b_original_rip,
            saved_context_b_original_flags, saved_context_b_original_rsp, 2);
        blocking_ipc_step = 2;
        serial_puts("LEANOS/10 IPC event=dispatch subject=1 address-space=1 blocked-subject=2 trusted=1\n");
        return;
    }
    if (current_subject == 2 && blocking_ipc_step == 3) {
        check_selected_root_b();
        if (target_owner != 2 || saved_owner != 1) fail("blocking-ipc-switch-b-owner");
        check_original_frame(target, saved_context_b_original_rip,
            saved_context_b_original_flags, saved_context_b_original_rsp, 2);
        blocking_ipc_step = 4;
        serial_puts("LEANOS/10 IPC event=dispatch subject=2 address-space=2 reservation=owned trusted=1\n");
        return;
    }
    if (current_subject == 2 && preemption_step == 2 && timer_accepted == 1) {
        check_selected_root_b();
        check_initial_b_frame(target);
        check_original_frame(saved_context_a, saved_context_a_original_rip,
            saved_context_a_original_flags,
            saved_context_a_original_rsp, saved_context_owner_a);
        check_resumable_witness(1, target, saved_context_a, target_owner, saved_owner,
            ORACLE_INDEX_RESUMABLE_A_TO_B);
        preemption_step = 3;
        serial_puts("LEANOS/5 SWITCH subject=2 address-space=2 cr3=switched stack=initial contexts=separate\n");
        return;
    }
    if (current_subject == 1 && preemption_step == 5 && timer_accepted == 2) {
        check_selected_root_a();
        check_original_frame(saved_context_b, saved_context_b_original_rip,
            saved_context_b_original_flags,
            saved_context_b_original_rsp, saved_context_owner_b);
        check_original_frame(target, saved_context_a_original_rip,
            saved_context_a_original_flags,
            saved_context_a_original_rsp, saved_context_owner_a);
        check_resumable_witness(2, target, saved_context_b, target_owner, saved_owner,
            ORACLE_INDEX_RESUMABLE_B_TO_A);
        preemption_step = 6;
        serial_puts("LEANOS/5 SWITCH subject=1 address-space=1 cr3=switched stack=resumed contexts=separate\n");
        return;
    }
    fail("switch-binding");
}

static void check_cross_bank_negative(void) {
    uint64_t crossed_target = saved_context_owner_b | (1ull << 8);
    uint64_t saved_b = saved_context_owner_b | (2ull << 8);
    if (leanos_resumable_preemption_demo(2, crossed_target, saved_b, 0x1c, 0xde) != 0)
        fail("cross-bank-negative");
}

static void check_initial_b_frame_negative(void) {
    uint64_t original_flags = initial_context_b[17];
    initial_context_b[17] = 0x206;
    if (initial_b_frame_valid(initial_context_b)) fail("initial-flags-negative");
    initial_context_b[17] = original_flags;
    check_initial_b_frame(initial_context_b);
}

static void arm_timer(void) {
    /* Legacy PIC remap: IRQ0 -> vector 32; all lines but IRQ0 remain masked. */
    out8(0x20, 0x11); out8(0xa0, 0x11);
    out8(0x21, 0x20); out8(0xa1, 0x28);
    out8(0x21, 0x04); out8(0xa1, 0x02);
    out8(0x21, 0x01); out8(0xa1, 0x01);
    out8(0x21, 0xfe); out8(0xa1, 0xff);
    /* PIT channel 0, mode 0, count 65535: a single terminal-count IRQ. */
    out8(0x43, 0x30); out8(0x40, 0xff); out8(0x40, 0xff);
}

uint64_t page_fault_handler(uint64_t error, uint64_t rip, uint64_t saved_cs,
                            uint64_t fault_address) {
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
    if ((saved_cs & 3u) == 3u && error == 5u &&
        rip == (uint64_t)user_a_fault_instruction && fault_address == 0u) {
        uint64_t cr3;
        __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
        if (current_subject != 1 || cr3 != (uint64_t)page_map_level_4_a ||
            saved_context_owner_b != 2 || !initial_b_frame_valid(initial_context_b))
            fail("fault-authority-binding");
        serial_puts("LEANOS/14 FAULT-ENTRY vector=14 error=5 origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 result=PASS\n");
        uint64_t result = leanos_fault_dispatch_demo(14, saved_cs & 3u,
            current_subject, current_subject, saved_context_owner_b,
            saved_context_owner_b);
        if (result != UINT64_C(0x00000000ff020202))
            fail("fault-model-dispatch");
        uint64_t selected = (result >> 8) & 0xffu;
        uint64_t address_space = (result >> 16) & 0xffu;
        uint64_t cleanup = (result >> 24) & 0x1fu;
        uint64_t peer_context_witness = (result >> 29) & 1u;
        uint64_t peer_capability_witness = (result >> 30) & 1u;
        uint64_t peer_resource_witness = (result >> 31) & 1u;
        if (cleanup != 0x1fu || peer_context_witness != 1 ||
            peer_capability_witness != 1 || peer_resource_witness != 1 ||
            selected != saved_context_owner_b || address_space != 2)
            fail("fault-model-encoding");
        fault_dispatch_attestation = result;
        current_subject = selected;
        serial_puts("LEANOS/14 TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS\n");
        serial_puts("LEANOS/14 DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS\n");
        return 2;
    }
#endif
    if ((saved_cs & 3u) == 3u && error == 5u &&
        rip == (uint64_t)user_a_fault_instruction && fault_address == 0u) {
#ifdef LEANOS_ENTRY_HIGH_WATER
        report_entry_stack_high_water("user-page-fault");
#endif
        serial_puts("LEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS\n");
        return (uint64_t)user_a_fault_recovered;
    }
    if (supervisor_probe == 1 && (saved_cs & 3u) == 0u && error == 3u &&
        rip == (uint64_t)wp_probe_instruction &&
        fault_address == (uint64_t)wp_probe_target) {
        serial_puts("LEANOS/4 PROBE kind=wp vector=14 error=3 origin=kernel address=kernel-text policy=fatal result=PASS\n");
        supervisor_probe = 2;
        return (uint64_t)wp_probe_recovered;
    }
    if (supervisor_probe == 3 && (saved_cs & 3u) == 0u && error == 17u &&
        rip == (uint64_t)user_a_entry && fault_address == (uint64_t)user_a_entry) {
        serial_puts("LEANOS/4 PROBE kind=smep vector=14 error=17 origin=kernel address=user-a-text policy=fatal result=PASS\n");
        supervisor_probe = 4;
        return (uint64_t)smep_probe_recovered;
    }
    if (supervisor_probe == 5 && (saved_cs & 3u) == 0u && error == 1u &&
        fault_address == (uint64_t)user_a_stack) {
        extern char smap_probe_recovered[];
        serial_puts("LEANOS/6 PROBE kind=smap-direct vector=14 origin=kernel ac=0 result=PASS\n");
        supervisor_probe = 6;
        return (uint64_t)smap_probe_recovered;
    }
    fail("kernel-fault");
}

/* The sole boot-reachable Lean runtime primitive. See docs/boot-image.md. */
uint8_t lean_uint64_dec_eq(uint64_t left, uint64_t right) {
    return (uint8_t)(left == right);
}

void kernel_main(uint32_t multiboot_magic, uint32_t multiboot_info) {
    serial_init();
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    serial_puts(extended_state_probe_class >= 5
        ? "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fast-entry-denial controls=wp,smep,smap,em,mp,ts,sce-off\n"
        : "LEANOS/13 BOOT target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts\n");
#elif defined(LEANOS_FAULT_CONTAINMENT_SCENARIO)
    serial_puts("LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment contract=v1 controls=wp,smep,smap\n");
#elif defined(LEANOS_PREEMPTION_SCENARIO)
    serial_puts("LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=bounded-two-shot-pit controls=wp,smep,smap\n");
#else
    serial_puts("LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap\n");
#endif

    quarantine_q35_pci_dma();

    check_boot_page_tables();

    boot_allocate(multiboot_magic, multiboot_info);

    replay_oracle();

    privilege_init();
    check_fast_entry_cpuid();
    check_fast_entry_control();
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    if (extended_state_probe_class >= 5)
        serial_puts("LEANOS/14 FAST-ENTRY cpu.vendor=AuthenticAMD mode=long64 syscall=1 sysenter=1 efer.sce=0 star=0 lstar=0 cstar=0 sfmask=0 sysenter.cs=0 sysenter.esp=0 sysenter.eip=0 writes=complete readback=exact result=PASS\n");
#endif
#ifdef LEANOS_DOUBLE_FAULT_PROBE
    run_double_fault_probe();
#endif
    enable_smep();
    uint64_t cr0, cr4;
    __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
    const uint64_t required_cr0 = (1ull << 16) | (1ull << 3) |
        (1ull << 2) | (1ull << 1);
    const uint64_t forbidden_cr4 =
        (1ull << 22) | (1ull << 18) | (1ull << 10) | (1ull << 9);
    if ((cr0 & required_cr0) != required_cr0 ||
        (cr4 & forbidden_cr4) != 0 ||
        (cr4 & (1ull << 20)) == 0 || (cr4 & (1ull << 21)) == 0) {
        fail("supervisor-controls");
    }
    record_extended_state_cpuid();
    serial_puts("LEANOS/6 CONTROL cr0.wp=1 cr0.em=1 cr0.mp=1 cr0.ts=1 cr4.osfxsr=0 cr4.osxmmexcpt=0 cr4.osxsave=0 cr4.pke=0 cr4.smep=1 cr4.smap=1 ac=0 stage=exception-path-ready\n");
    supervisor_probe = 1;
    run_wp_probe();
    if (supervisor_probe != 2) fail("wp-no-fault");
    supervisor_probe = 3;
    run_smep_probe();
    if (supervisor_probe != 4) fail("smep-no-fault");
    supervisor_probe = 5;
    run_smap_probe();
    if (supervisor_probe != 6) fail("smap-no-fault");
    exercise_copy_policy();
    smap_omit_cleanup_probe();
    if (!ac_is_set()) fail("cleanup-probe-undetected");
    smap_force_clac();
    if (ac_is_set()) fail("cleanup-recovery");
    serial_puts("LEANOS/6 CLEANUP omitted=detected wrappers=checked entry=clac result=PASS\n");
    check_cross_bank_negative();
    check_initial_b_frame_negative();
#ifdef LEANOS_EXTENDED_STATE_SCENARIO
    current_subject = 1;
    __asm__ volatile ("mov %0, %%cr3" : : "r"(page_map_level_4_a) : "memory");
    if (extended_state_probe_class > 6)
        fail("extended-state-probe-class");
    serial_puts(extended_state_probe_class >= 5
        ? "LEANOS/14 FAST-ENTRY event=enter subject=1 address-space=1 instruction="
        : "LEANOS/13 EXTENDED-STATE event=enter subject=1 address-space=1 instruction=");
    serial_puts(extended_state_probe_class == 0 ? "x87" :
        extended_state_probe_class == 1 ? "mmx" :
        extended_state_probe_class == 2 ? "sse" :
        extended_state_probe_class == 3 ? "sse2" :
        extended_state_probe_class == 4 ? "avx" :
        extended_state_probe_class == 5 ? "syscall" : "sysenter");
    serial_puts(extended_state_probe_class >= 2 ?
        " expected-vector=6\n" : " expected-vector=7\n");
    enter_user(user_a_entry, user_a_stack_top);
#elif defined(LEANOS_FAULT_CONTAINMENT_SCENARIO)
    current_subject = 1;
    __asm__ volatile ("mov %0, %%cr3" : : "r"(page_map_level_4_a) : "memory");
    check_selected_root_a();
    serial_puts("LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned\n");
    enter_user(user_a_entry, user_a_stack_top);
#elif defined(LEANOS_PREEMPTION_SCENARIO)
    arm_timer();
    enter_user(user_a_entry, user_a_stack_top);
#else
    current_subject = 2;
    __asm__ volatile ("mov %0, %%cr3" : : "r"(page_map_level_4_b) : "memory");
    check_selected_root_b();
    serial_puts("LEANOS/10 IPC event=enter subject=2 address-space=2 cpl=3 endpoint=10\n");
    enter_user(user_b_entry, user_b_stack_top);
#endif
    fail("iret-returned");
}
