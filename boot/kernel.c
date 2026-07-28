#include <stdint.h>
#include "corpus.h"
#include "generated-boundary-abi.h"
#include "leanos/composite-dispatcher.h"
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
extern uint64_t leanos_boot_handoff_stream_init(uint64_t, uint64_t, uint64_t,
                                                uint64_t, uint64_t);
extern uint64_t leanos_boot_handoff_stream_step(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_init(uint64_t, uint64_t, uint64_t,
                                        uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_step(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_manifest_candidate(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_manifest_start(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_select_frame(uint64_t, uint64_t, uint64_t,
                                         uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_publish_authority(uint64_t, uint64_t, uint64_t,
                                              uint64_t, uint64_t, uint64_t,
                                              uint64_t);
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
extern uint64_t leanos_nmi_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                uint64_t);
extern uint64_t leanos_boot_phase_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                       uint64_t);
extern uint64_t leanos_stale_translation_demo(uint64_t, uint64_t, uint64_t,
                                              uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_page_fault_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                       uint64_t);
extern uint64_t leanos_authorize_page_fault_snapshot(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_page_fault_dispatch_transition(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t,
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
extern void isr0(void);
extern void isr2(void);
extern void isr3(void);
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
extern char user_a_write_fault_instruction[], user_a_write_fault_recovered[];
extern char user_a_write_target[];
extern char user_a_nx_fault_instruction[], user_a_nx_fault_recovered[];
extern char user_a_reserved_fault_instruction[], user_a_reserved_fault_recovered[];
extern void disable_nxe_for_reserved_fault(void);
#if defined(LEANOS_ENTRY_ADVERSARIAL) || defined(LEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO)
extern char user_a_direct_port_probe[];
#endif
#ifdef LEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO
extern const uint64_t direct_port_probe_class;
#endif
#ifdef LEANOS_INTEGER_FAULT_SCENARIO
extern const uint64_t integer_fault_probe_class;
extern char user_a_divide_instruction[], user_a_breakpoint_after[];
#endif
extern const uint64_t page_fault_probe_class;
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
extern char smap_probe_instruction[], smap_probe_recovered[];
extern char __boot_image_start[], __boot_image_end[];
extern char __df_ist_stack_start[], __df_ist_stack_end[];
extern char __df_ist_guard_start[], __df_ist_guard_end[];
extern char __nmi_ist_guard_start[], __nmi_ist_guard_end[];
extern char __nmi_ist_stack_start[], __nmi_ist_stack_end[];
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
#define PTE_GLOBAL (1ull << 8)
#define PTE_NX (1ull << 63)
#define PTE_ADDRESS 0x000ffffffffff000ull

struct __attribute__((packed)) mb2_tag { uint32_t type, size; };
struct __attribute__((packed)) mb2_mmap_tag {
    uint32_t type, size, entry_size, entry_version;
};
struct __attribute__((packed)) mb2_mmap_entry {
    uint64_t base, length; uint32_t type, reserved;
};

/* Written once during bounded boot ingestion, then treated as immutable by
   the parser.  Only chunks exposed by the generated stream transition enter
   this copy. */
static uint8_t boot_handoff_copy[MAX_HANDOFF_BYTES]
    __attribute__((aligned(8)));
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
#ifdef LEANOS_PAGE_FAULT_PROBE_RESERVED_BIT
volatile uint64_t reserved_fault_nxe_disabled;
#endif

/* The machine-facing spelling of InterruptEntry's version-one canonical
   page-fault encoding.  Construction is confined to
   authorize_page_fault_snapshot; every operation-specific consumer receives
   the same const object after the generated provenance agreement succeeds. */
struct page_fault_entry_record {
    uint64_t version;
    uint64_t vector;
    uint64_t error;
    uint64_t fault_address;
    uint64_t fault_page;
    uint64_t access;
    uint64_t protection;
    uint64_t user;
    uint64_t current_subject;
    uint64_t active_address_space;
    uint64_t active_cr3;
    uint64_t paging_controls;
    uint64_t rip;
    uint64_t saved_cs;
    uint64_t rflags;
    uint64_t user_rsp;
    uint64_t user_ss;
    uint64_t stack_identity;
    uint64_t reserved;
};

_Static_assert(sizeof(struct page_fault_entry_record) == 19u * sizeof(uint64_t),
               "canonical page-fault record layout");

enum page_fault_transition_kind {
    PAGE_FAULT_TRANSITION_CONTAIN = 1,
    PAGE_FAULT_TRANSITION_FATAL = 2,
    PAGE_FAULT_TRANSITION_KERNEL_DIAGNOSTIC = 3,
    PAGE_FAULT_TRANSITION_REJECTED = 4
};

struct page_fault_transition {
    enum page_fault_transition_kind kind;
    uint64_t result;
    const struct page_fault_entry_record *snapshot;
};
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
volatile unsigned ordinary_entry_active;
volatile uint64_t nmi_runtime_canary = UINT64_C(0x52554e54494d454e);
#ifdef LEANOS_ENTRY_HIGH_WATER
static uint64_t entry_stack_high_water_pattern = UINT64_C(0x6c65616e6f735741);
#endif
#ifdef LEANOS_ENTRY_ADVERSARIAL
static unsigned entry_adversarial_step;
#endif
#if defined(LEANOS_ENTRY_ADVERSARIAL) || defined(LEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO)
static uint64_t direct_port_fault_attestation;
#endif
#ifdef LEANOS_INTEGER_FAULT_SCENARIO
static uint64_t integer_fault_attestation;
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
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
static void report_page_fault_snapshot(
    const struct page_fault_entry_record *snapshot,
    uint64_t authorization, uint64_t route,
    uint64_t expected_leaf, uint64_t live_leaf);
static __attribute__((noreturn)) void report_page_fault_terminal(
    const struct page_fault_entry_record *snapshot, uint64_t authorization,
    uint64_t route, uint64_t expected_leaf, uint64_t live_leaf);
#endif
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
    uint64_t efer_denied = (1ull << 8) | (1ull << 10) | (1ull << 11);
#ifdef LEANOS_PAGE_FAULT_PROBE_RESERVED_BIT
    if (reserved_fault_nxe_disabled)
        efer_denied &= ~(1ull << 11);
#endif
    if ((state[0] & efer_model_mask) != efer_denied)
        fail("fast-entry-efer-readback");
    for (unsigned i = 1; i < 8; ++i)
        if (state[i] != 0) fail("fast-entry-target-readback");
}

/* Read the descriptor selected by the live task register rather than trusting
   only the C initializer.  x86 keeps hidden descriptor state after LTR, which
   is part of the documented machine-semantics assumption; STR plus SGDT bind
   the selected descriptor and the stored TSS image that can be reloaded. */
static void check_direct_port_control(unsigned report) {
    struct descriptor gdtr;
    uint16_t task_selector;
    uint64_t flags;
    __asm__ volatile ("sgdt %0" : "=m"(gdtr));
    __asm__ volatile ("str %0" : "=r"(task_selector));
    __asm__ volatile ("pushfq; pop %0" : "=r"(flags) : : "memory");
    if (task_selector != 0x28 || gdtr.base != (uint64_t)gdt64 ||
        gdtr.limit < 0x37)
        fail("direct-port-task-register");
    const uint64_t low = *(const uint64_t *)(gdtr.base + task_selector);
    const uint64_t high = *(const uint64_t *)(gdtr.base + task_selector + 8u);
    const uint64_t limit = (low & 0xffffu) | ((low >> 32) & 0xf0000u);
    const uint64_t base = ((low >> 16) & 0xffffffu) |
        ((low >> 32) & 0xff000000u) | (high << 32);
    if (limit != sizeof(tss) - 1 || base != (uint64_t)&tss ||
        ((low >> 40) & 0xfu) != 0xbu || ((low >> 47) & 1u) != 1u ||
        ((low >> 55) & 1u) != 0u ||
        tss.iomap != sizeof(tss) || ((flags >> 12) & 3u) != 0)
        fail("direct-port-control-readback");
    if (report) {
        serial_puts("LEANOS/16 DIRECT-PORT-CONTROL tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS\n");
    }
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
    if (vector == 0) { expected_error = 0; dpl = 0; purpose = 7; }
    else if (vector == 3) { expected_error = 0; dpl = 3; purpose = 8; }
    else if (vector == 6) { expected_error = 0; dpl = 0; purpose = 4; }
    else if (vector == 7) { expected_error = 0; dpl = 0; purpose = 5; }
    else if (vector == 13) { expected_error = 1; dpl = 0; purpose = 6; }
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
    /* Every ordinary gate, including the broad vector-13 general-protection
       class, must match the same generated InterruptEntry manifest.  The
       handler refines vector 13 only after checking its cause and operands. */
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
        { 0, isr0, 0, 0x8e }, { 2, isr2, 2, 0x8e },
        { 3, isr3, 0, 0xee },
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
        tss.ist[0] != (uint64_t)__df_ist_stack_end ||
        tss.ist[1] != (uint64_t)__nmi_ist_stack_end)
        fail("entry-tss-mismatch");
    serial_puts("LEANOS/17 ENTRY-MANIFEST ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS\n");
}

#ifdef LEANOS_ENTRY_ADVERSARIAL
uint64_t entry_adversarial_gp_handler(uint64_t error, uint64_t rip,
                                      uint64_t saved_cs, uint64_t saved_rdx,
                                      uint64_t saved_rax) {
    static const uint64_t expected_error[] = { 14u * 8u + 2u, 32u * 8u + 2u };
    if (saved_cs != 0x23 || entry_adversarial_step >= 3)
        fail("entry-adversarial-gp");
    if (entry_adversarial_step == 2) {
        uint64_t cr3;
        __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
        uint64_t port = saved_rdx & UINT64_C(0xffff);
        uint64_t value = saved_rax & UINT64_C(0xff);
        if (error != 0 || rip != (uint64_t)user_a_direct_port_probe ||
            port != DEBUG_EXIT || value != UINT64_C(0x11) ||
            current_subject != 1 || cr3 != (uint64_t)page_map_level_4_a)
            fail("direct-port-gp-binding");
        check_direct_port_control(0);
        if (leanos_direct_port_io_demo(0, 0, 0, port, 1, value) !=
            UINT64_C(0x0144332211))
            fail("direct-port-model-denial");
        if (blocking_ipc_step != 2 || saved_context_owner_b != 2 ||
            saved_context_b[15] != saved_context_b_original_rip ||
            saved_context_b[17] != saved_context_b_original_flags ||
            saved_context_b[18] != saved_context_b_original_rsp ||
            saved_context_b[16] != 0x23 || saved_context_b[19] != 0x1b)
            fail("direct-port-peer-context");
        /* DirectPortIO first types the architectural #GP(0) denial; the
           canonical contained-user-fault class then reuses the existing
           atomic cleanup/survivor-dispatch adapter. */
        uint64_t result = leanos_fault_dispatch_demo(14, saved_cs & 3u,
            current_subject, current_subject, saved_context_owner_b,
            saved_context_owner_b);
        if (result != UINT64_C(0x00000000ff020202))
            fail("direct-port-fault-dispatch");
        uint64_t selected = (result >> 8) & 0xffu;
        uint64_t address_space = (result >> 16) & 0xffu;
        uint64_t cleanup = (result >> 24) & 0x1fu;
        if (selected != saved_context_owner_b || address_space != 2 ||
            cleanup != 0x1fu || ((result >> 29) & 7u) != 7u)
            fail("direct-port-fault-encoding");
        direct_port_fault_attestation = result;
        current_subject = selected;
        serial_puts("LEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=244 direction=out width=byte purpose=user device-mutation=0 result=PASS\n");
        serial_puts("LEANOS/16 DIRECT-PORT-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS\n");
        serial_puts("LEANOS/16 DIRECT-PORT-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS\n");
        ++entry_adversarial_step;
        return 2;
    }
    if (error != expected_error[entry_adversarial_step])
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
    uint64_t nmi_guard = boot_page(__nmi_ist_guard_start);
    expect_live_mutation_rejected("nmi-guard-mapping", &page_table_b[nmi_guard],
        nmi_guard * PAGE_BYTES | PTE_PRESENT | PTE_WRITABLE | PTE_NX,
        "pt", nmi_guard);
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

__attribute__((noinline, used))
static void activate_user_address_space(uint64_t *root) {
    __asm__ volatile ("mov %0, %%cr3" : : "r"(root) : "memory");
}

__attribute__((noinline, used))
static uint64_t invalidate_snapshot_fault_page(
    const struct page_fault_entry_record *snapshot) {
    const uint64_t fault_address = snapshot->fault_address;
    __asm__ volatile ("invlpg (%0)" : : "r"(fault_address) : "memory");
    return fault_address / PAGE_BYTES == snapshot->fault_page;
}

static void serial_u64(uint64_t value) {
    char digits[21]; unsigned length = 0;
    if (value == 0) { serial_putc('0'); return; }
    while (value != 0) { digits[length++] = (char)('0' + value % 10); value /= 10; }
    while (length != 0) serial_putc(digits[--length]);
}

#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
static void report_page_fault_snapshot(
    const struct page_fault_entry_record *snapshot,
    uint64_t authorization, uint64_t route,
    uint64_t expected_leaf, uint64_t live_leaf) {
    const uint64_t words[19] = {
        snapshot->version, snapshot->vector, snapshot->error,
        snapshot->fault_address, snapshot->fault_page, snapshot->access,
        snapshot->protection, snapshot->user, snapshot->current_subject,
        snapshot->active_address_space, snapshot->active_cr3,
        snapshot->paging_controls, snapshot->rip, snapshot->saved_cs,
        snapshot->rflags, snapshot->user_rsp, snapshot->user_ss,
        snapshot->stack_identity, snapshot->reserved
    };
    serial_puts("LEANOS/14 PF-WALK page="); serial_u64(snapshot->fault_page);
    serial_puts(" expected-leaf="); serial_u64(expected_leaf);
    serial_puts(" live-leaf="); serial_u64(live_leaf);
    serial_puts(page_fault_probe_class == 2
        ? " cause=no-execute denial=no-execute result=PASS\n"
        : page_fault_probe_class == 1
        ? " cause=not-writable denial=not-writable result=PASS\n"
        : " cause=supervisor denial=supervisor result=PASS\n");
    serial_puts("LEANOS/14 PF-SNAPSHOT codec=1 width=19 words=");
    for (unsigned i = 0; i < 19; ++i) {
        if (i != 0) serial_putc(',');
        serial_u64(words[i]);
    }
    serial_puts(" authorization="); serial_u64(authorization);
    serial_puts(" route="); serial_u64(route);
    serial_puts(" result=PASS\n");
}

static __attribute__((noreturn)) void report_page_fault_terminal(
    const struct page_fault_entry_record *snapshot, uint64_t authorization,
    uint64_t route, uint64_t expected_leaf, uint64_t live_leaf) {
    serial_puts("LEANOS/14 PF-TERMINAL codec=1 case=");
    serial_puts(page_fault_probe_class == 3 ? "reserved-bit" : "walk-mismatch");
    serial_puts(" vector=14 error="); serial_u64(snapshot->error);
    serial_puts(" access="); serial_puts(snapshot->access == 2 ? "execute" :
        snapshot->access == 1 ? "write" : "read");
    serial_puts(" cr2="); serial_u64(snapshot->fault_address);
    serial_puts(" rip=");
    serial_puts(page_fault_probe_class == 3
        ? "user-a-reserved-fault-instruction"
        : "user-a-fault-instruction");
    serial_puts(" expected-leaf="); serial_u64(expected_leaf);
    serial_puts(" live-leaf="); serial_u64(live_leaf);
    serial_puts(" authorization="); serial_u64(authorization);
    serial_puts(" route="); serial_u64(route);
    serial_puts(" halt=absorbing containment=0 cleanup=0 dispatch=0 return=none\n");
    finish(0x12);
}
#endif

static unsigned canonical(uint64_t value) {
    uint64_t high = value >> 47;
    return high == 0 || high == 0x1ffffu;
}

static void verify_q35_pci_dma(void);
#if LEANOS_RETURN_CORRUPTION_MODE == 25
static __attribute__((noinline, noipa)) void inject_dma_bus_master_reenable(void);
#endif

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
#if LEANOS_RETURN_CORRUPTION_MODE == 22
    case 22: return "direct-port-bitmap-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 23
    case 23: return "direct-port-limit-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 24
    case 24: return "direct-port-granularity-relaxation";
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 25
    case 25: return "dma-bus-master-reenable";
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
    serial_puts(mode >= 14 && mode <= 25
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
#if LEANOS_RETURN_CORRUPTION_MODE == 22
    case 22:
        tss.iomap = sizeof(tss) - 1;
        break;
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 23
    case 23:
        gdt64[5] = (gdt64[5] & ~UINT64_C(0xffff)) | (sizeof(tss) - 2);
        break;
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 24
    case 24:
        gdt64[5] |= UINT64_C(1) << 55;
        break;
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 25
    case 25:
        inject_dma_bus_master_reenable();
        break;
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
    check_direct_port_control(0);
    verify_q35_pci_dma();
    /* Accepted ordinary entries remain armed through handler dispatch and
       context selection.  Clear only in this final validated return gate;
       initial boot dispatch is intentionally unarmed. */
    if (ordinary_entry_active) ordinary_entry_active = 0;
}

static __attribute__((noreturn)) void handoff_fail(const char *reason) {
    serial_puts("LEANOS/7 BOOTALLOC status=FAIL reason="); serial_puts(reason);
    serial_putc('\n'); finish(0x11);
}

struct boot_handoff_stream_state {
    uint64_t version, status, error, identity, extent, offset, chain;
};

static uint64_t handoff_stream_init_query(uint32_t magic, uint32_t info_address,
                                          uint32_t total, uint64_t query) {
    return leanos_boot_handoff_stream_init(
        magic, info_address, total, info_address, query);
}

static uint64_t handoff_stream_step_query(
        const struct boot_handoff_stream_state *state, uint32_t info_address,
        uint64_t offset, uint64_t chunk, uint64_t terminal, uint64_t query) {
    return leanos_boot_handoff_stream_step(
        state->version, state->status, state->error, state->identity,
        state->extent, state->offset, state->chain, info_address, offset, 8,
        chunk, terminal, query);
}

/* Physical memory access is the explicit TCB boundary.  The generated scalar
   transition binds every accepted eight-byte chunk to one aligned identity
   and extent, enforces exact offsets and terminal state, and exposes the word
   copied below only on success. */
static const uint8_t *copy_boot_handoff(uint32_t magic, uint32_t info_address,
                                        uint32_t total) {
    const uint8_t *physical = (const uint8_t *)(uint64_t)info_address;
    struct boot_handoff_stream_state state = {
        handoff_stream_init_query(magic, info_address, total, 0),
        handoff_stream_init_query(magic, info_address, total, 1),
        handoff_stream_init_query(magic, info_address, total, 2),
        handoff_stream_init_query(magic, info_address, total, 3),
        handoff_stream_init_query(magic, info_address, total, 4),
        handoff_stream_init_query(magic, info_address, total, 5),
        handoff_stream_init_query(magic, info_address, total, 6)
    };
    if (state.version != 2 || state.status != 0 || state.error != 0 ||
        state.identity != info_address || state.extent != total ||
        state.offset != 0)
        handoff_fail("stream-init");

    for (uint64_t offset = 0; offset < total; offset += 8) {
        uint64_t physical_chunk = *(const uint64_t *)(physical + offset);
#ifdef LEANOS_MALFORMED_HANDOFF_FIXTURE
        /* Controlled production-decoder negative: preserve the advertised
           extent while making the Multiboot information-header reserved word
           nonzero.  The generated stream transport must bind this exact raw
           word and the generated decoder must reject it before authority. */
        if (offset == 0) physical_chunk |= 1ull << 32;
#endif
        uint64_t terminal = offset + 8 == total;
        struct boot_handoff_stream_state next = {
            handoff_stream_step_query(
                &state, info_address, offset, physical_chunk, terminal, 0),
            handoff_stream_step_query(
                &state, info_address, offset, physical_chunk, terminal, 1),
            handoff_stream_step_query(
                &state, info_address, offset, physical_chunk, terminal, 2),
            handoff_stream_step_query(
                &state, info_address, offset, physical_chunk, terminal, 3),
            handoff_stream_step_query(
                &state, info_address, offset, physical_chunk, terminal, 4),
            handoff_stream_step_query(
                &state, info_address, offset, physical_chunk, terminal, 5),
            handoff_stream_step_query(
                &state, info_address, offset, physical_chunk, terminal, 6)
        };
        uint64_t exposed = handoff_stream_step_query(
            &state, info_address, offset, physical_chunk, terminal, 7);
        uint64_t exposed_count = handoff_stream_step_query(
            &state, info_address, offset, physical_chunk, terminal, 8);
        if (next.version != 2 || next.error != 0 ||
            next.identity != info_address || next.extent != total ||
            next.offset != offset + 8 || exposed_count != 8 ||
            exposed != physical_chunk ||
            next.status != (terminal ? 1u : 0u))
            handoff_fail("stream-step");
        *(uint64_t *)(boot_handoff_copy + offset) = exposed;
        state = next;
    }
    if (state.status != 1 || state.offset != total)
        handoff_fail("stream-incomplete");
    return boot_handoff_copy;
}

struct boot_decode_state { uint64_t word[19]; };

#define BOOT_MANIFEST_ARGS(info_address, total) \
    0, 0x100000u, \
    (uint64_t)__boot_image_start, \
    (uint64_t)__boot_image_end - (uint64_t)__boot_image_start, \
    (uint64_t)page_map_level_4_a, \
    (uint64_t)(page_table_b + BOOT_LEAF_COUNT) - (uint64_t)page_map_level_4_a, \
    (uint64_t)gdt64, sizeof(uint64_t) * 7u, \
    (uint64_t)boot_stack, (uint64_t)boot_stack_top - (uint64_t)boot_stack, \
    (uint64_t)__entry_stack_guard_start, \
    (uint64_t)__entry_stack_guard_end - (uint64_t)__entry_stack_guard_start, \
    (uint64_t)__entry_stack_start, \
    (uint64_t)__entry_stack_end - (uint64_t)__entry_stack_start, \
    (uint64_t)__user_a_text_start, \
    (uint64_t)__user_b_stack_end - (uint64_t)__user_a_text_start, \
    (uint64_t)(info_address), (uint64_t)(total)

static struct boot_decode_state decode_boot_candidate(
        uint32_t magic, uint32_t info_address, uint32_t total,
        uint64_t candidate, const uint8_t *info) {
    struct boot_decode_state state, next;
    for (uint64_t query = 0; query < 19; ++query)
        state.word[query] =
            leanos_boot_decode_init(magic, info_address, total, candidate, query);
    if (state.word[0] != 4 || state.word[1] != 0 || state.word[2] != 0 ||
        state.word[3] != info_address || state.word[4] != total ||
        state.word[5] != 0 || state.word[16] != candidate ||
        state.word[18] != 0)
        handoff_fail("decode-init");
    for (uint64_t offset = 0; offset < total; offset += 8) {
        uint64_t chunk = *(const uint64_t *)(info + offset);
        uint64_t terminal = offset + 8 == total;
        for (uint64_t query = 0; query < 19; ++query)
            next.word[query] = leanos_boot_decode_step(
                state.word[0], state.word[1], state.word[2], state.word[3],
                state.word[4], state.word[5], state.word[6], state.word[7],
                state.word[8], state.word[9], state.word[10], state.word[11],
                state.word[12], state.word[13], state.word[14], state.word[15],
                state.word[16], state.word[17], state.word[18], info_address,
                offset, chunk, terminal, query);
        state = next;
        if (state.word[2] != 0)
            handoff_fail("decode-rejected");
    }
    if (state.word[1] != 1 || state.word[5] != total || state.word[7] != 7)
        handoff_fail("decode-incomplete");
    return state;
}

/* The generated raw-word decoder is the sole tag walker, classifier,
   reservation decision, and first-frame selector.  C only transports the
   immutable copy and executes the returned scrub/publication operation. */
static void boot_allocate(uint32_t magic, uint32_t info_address) {
    if (magic != MULTIBOOT2_RUNTIME_MAGIC) handoff_fail("magic");
    if ((info_address & 7u) != 0 || info_address < PAGE_BYTES ||
        info_address >= BOOT_ACCESSIBLE_LIMIT) handoff_fail("pointer");
    const uint8_t *physical = (const uint8_t *)(uint64_t)info_address;
    uint32_t total = *(const uint32_t *)physical;
    if (total < 16 || total > MAX_HANDOFF_BYTES || (total & 7u) != 0 ||
        total > BOOT_ACCESSIBLE_LIMIT - info_address) handoff_fail("bounds");
    const uint8_t *info = copy_boot_handoff(magic, info_address, total);
    uint64_t first = leanos_boot_manifest_start(BOOT_MANIFEST_ARGS(info_address, total));
    if (first >= 4096) handoff_fail("manifest");
    uint64_t selected = 4096;
    struct boot_decode_state authority = {{0}};
    for (uint64_t candidate = first; candidate < 4096 && selected == 4096;
         ++candidate) {
        struct boot_decode_state decoded =
            decode_boot_candidate(magic, info_address, total, candidate, info);
        uint64_t manifest = leanos_boot_manifest_candidate(
            candidate, BOOT_MANIFEST_ARGS(info_address, total));
        selected = leanos_boot_select_frame(
            selected, candidate, decoded.word[1], decoded.word[14],
            decoded.word[15], manifest);
        if (selected < 4096) authority = decoded;
    }
    if (selected >= 4096 || authority.word[16] != selected)
        handoff_fail("no-frame");

    volatile uint8_t *frame = (volatile uint8_t *)(selected * PAGE_BYTES);
    for (uint64_t i = 0; i < PAGE_BYTES; ++i) frame[i] = 0;
    for (uint64_t i = 0; i < PAGE_BYTES; ++i)
        if (frame[i] != 0) handoff_fail("scrub");
    uint64_t manifest = leanos_boot_manifest_candidate(
        selected, BOOT_MANIFEST_ARGS(info_address, total));
    published_boot_object = leanos_boot_publish_authority(
        selected, authority.word[16], authority.word[1], authority.word[14],
        authority.word[15], manifest, 1);
    if (published_boot_object != selected + 1) handoff_fail("publication");

    serial_puts("LEANOS/7 HANDOFF magic=valid info-bytes="); serial_u64(total);
    serial_puts(" mmap-entries="); serial_u64(authority.word[11]);
    serial_puts(" result=PASS\n");
    serial_puts("LEANOS/7 MAP boot-pages=4096");
    serial_puts(" reported-top-mib=");
    serial_u64(authority.word[17] / (1024u * 1024u));
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
    uint8_t required, bridge, multifunction;
};

/* This is the C rendering of DMAQuarantine.q35Manifest for topology version
   0x0008_0002_0002. Configuration mechanism #1 and the behavior of these
   devices remain trusted hardware/QEMU inputs; acceptance is integration
   evidence and is not a refinement theorem for the Lean snapshot. */
static const struct pci_manifest_entry q35_pci_manifest[] = {
    { 0, 0, 0x8086, 0x29c0, 0x060000, 1, 0, 0 },
    { 1, 0, 0x1234, 0x1111, 0x030000, 1, 0, 0 },
    { 3, 0, 0x1af4, 0x1000, 0x020000, 0, 0, 0 },
    { 31, 0, 0x8086, 0x2918, 0x060100, 1, 1, 1 },
    { 31, 2, 0x8086, 0x2922, 0x010601, 1, 0, 1 },
    { 31, 3, 0x8086, 0x2930, 0x0c0500, 1, 0, 1 },
};

struct pci_snapshot_entry {
    uint16_t vendor, product;
    uint32_t class_code;
    uint16_t command_before, command_after;
    uint8_t present, bridge, multifunction;
};

/* The one canonical live PCI observation. Boot fills it from hardware, the
   generated q35 snapshot validator consumes its compact canonical projection,
   and every later CPL3 return compares hardware with this same state. */
struct pci_live_snapshot {
    struct pci_snapshot_entry functions[
        sizeof(q35_pci_manifest) / sizeof(q35_pci_manifest[0])];
    uint64_t generated_result;
};

static struct pci_live_snapshot q35_live_pci_snapshot;

static uint64_t pci_snapshot_identity_word(
        const struct pci_snapshot_entry *entry) {
    return (uint64_t)entry->vendor |
        (uint64_t)entry->product << 16 |
        (uint64_t)entry->class_code << 32;
}

static uint64_t pci_snapshot_control_word(
        const struct pci_snapshot_entry *entry) {
    return (uint64_t)(entry->present ? 1u : 0u) |
        (uint64_t)entry->command_after << 2 |
        (uint64_t)entry->bridge << 14 |
        (uint64_t)entry->multifunction << 15;
}

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
            if ((command & ~PCI_COMMAND_MODEL_MASK) != 0)
                fail("dma-command-model");
            if ((command & PCI_COMMAND_BUS_MASTER) != 0) {
                ++initially_bus_mastering;
                initial_bus_master_mask |= 1u << index;
            }
            /* q35Snapshot's deny-all handoff is the exact all-zero Command
               projection, not merely any state with bus mastering clear. */
            uint16_t expected_command = 0;
            q35_live_pci_snapshot.functions[index].present = 1;
            q35_live_pci_snapshot.functions[index].vendor = vendor;
            q35_live_pci_snapshot.functions[index].product = product;
            q35_live_pci_snapshot.functions[index].class_code = class_code;
            q35_live_pci_snapshot.functions[index].command_before = command;
            pci_config_command(device, function, expected_command);
            ++writes;
            command = (uint16_t)pci_config_dword(device, function, 0x04);
            q35_live_pci_snapshot.functions[index].command_after = command;
            ++readbacks;
            if (command != expected_command)
                fail("dma-command-readback");
            seen |= 1u << index;
            ++present;
        }
    }

    unsigned optional_absent = 0;
    for (unsigned i = 0;
         i < sizeof(q35_pci_manifest) / sizeof(q35_pci_manifest[0]); ++i) {
        q35_live_pci_snapshot.functions[i].bridge =
            q35_pci_manifest[i].bridge;
        q35_live_pci_snapshot.functions[i].multifunction =
            q35_pci_manifest[i].multifunction;
        if (seen & (1u << i)) continue;
        if (q35_pci_manifest[i].required) fail("dma-required-missing");
        ++optional_absent;
    }
    if (present == 0) fail("dma-empty-inventory");
    if (present != 5 || optional_absent != 1 || writes != present ||
        readbacks != present)
        fail("dma-q35-nic-none");

    /* Feed the canonical live identity/status/Command/assignment/bridge
       projection itself through the generated q35Snapshot boundary. */
    q35_live_pci_snapshot.generated_result =
        leanos_validate_q35_dma_snapshot(
            1, UINT64_C(0x000800020002),
            pci_snapshot_identity_word(&q35_live_pci_snapshot.functions[0]),
            pci_snapshot_control_word(&q35_live_pci_snapshot.functions[0]),
            pci_snapshot_identity_word(&q35_live_pci_snapshot.functions[1]),
            pci_snapshot_control_word(&q35_live_pci_snapshot.functions[1]),
            pci_snapshot_identity_word(&q35_live_pci_snapshot.functions[2]),
            pci_snapshot_control_word(&q35_live_pci_snapshot.functions[2]),
            pci_snapshot_identity_word(&q35_live_pci_snapshot.functions[3]),
            pci_snapshot_control_word(&q35_live_pci_snapshot.functions[3]),
            pci_snapshot_identity_word(&q35_live_pci_snapshot.functions[4]),
            pci_snapshot_control_word(&q35_live_pci_snapshot.functions[4]),
            pci_snapshot_identity_word(&q35_live_pci_snapshot.functions[5]),
            pci_snapshot_control_word(&q35_live_pci_snapshot.functions[5]));
    if (q35_live_pci_snapshot.generated_result != 0)
        fail("dma-global-policy");

    for (unsigned i = 0;
         i < sizeof(q35_pci_manifest) / sizeof(q35_pci_manifest[0]); ++i) {
        const struct pci_manifest_entry *entry = &q35_pci_manifest[i];
        serial_puts("LEANOS/15 DMA-FUNCTION manifest=1 topology=000800020002 bdf=0:");
        serial_u64(entry->device);
        serial_putc('.');
        serial_u64(entry->function);
        serial_puts(" present=");
        serial_u64(q35_live_pci_snapshot.functions[i].present);
        serial_puts(" vendor=");
        serial_u64(q35_live_pci_snapshot.functions[i].present ? entry->vendor : 0);
        serial_puts(" device=");
        serial_u64(q35_live_pci_snapshot.functions[i].present ? entry->product : 0);
        serial_puts(" class=");
        serial_u64(q35_live_pci_snapshot.functions[i].present ? entry->class_code : 0);
        serial_puts(" command-before=");
        serial_u64(q35_live_pci_snapshot.functions[i].command_before);
        serial_puts(" command-after=");
        serial_u64(q35_live_pci_snapshot.functions[i].command_after);
        serial_puts(" assigned=0 bridge=");
        serial_u64(entry->bridge);
        serial_puts(" multifunction=");
        serial_u64(entry->multifunction);
        serial_puts(" policy=accepted\n");
    }
    serial_puts("LEANOS/15 DMA snapshot=1 topology=000800020002 bus=0 scanned=256 present=5 optional-absent=1 writes=5 readbacks=5 initial-bus-masters=");
    serial_u64(initially_bus_mastering);
    serial_puts(" initial-bus-master-mask=");
    serial_u64(initial_bus_master_mask);
    serial_puts(" bus-master=disabled readback=exact generated-result=");
    serial_u64(q35_live_pci_snapshot.generated_result);
    serial_puts(" stage=pre-cpl3 result=PASS\n");
}

/* Re-observe the complete finite inventory at every outbound CPL3 gate.  The
   full post-quarantine Command word, not just its bus-master bit, must remain
   identical to the boot observation.  This path is read-only in production. */
static __attribute__((noinline, noipa)) void verify_q35_pci_dma(void) {
    unsigned seen = 0, present = 0;
    for (unsigned device = 0; device < 32; ++device) {
        for (unsigned function = 0; function < 8; ++function) {
            uint32_t identity = pci_config_dword(device, function, 0x00);
            uint16_t vendor = (uint16_t)identity;
            if (vendor == UINT16_MAX) continue;

            unsigned index = 0;
            const struct pci_manifest_entry *entry =
                q35_manifest_entry(device, function, &index);
            if (!entry || (seen & (1u << index))) fail("dma-live-inventory");
            uint16_t product = (uint16_t)(identity >> 16);
            uint32_t class_code = pci_config_dword(device, function, 0x08) >> 8;
            uint8_t header = (uint8_t)(pci_config_dword(
                device, function, 0x0c) >> 16);
            if (vendor != entry->vendor || product != entry->product ||
                class_code != entry->class_code ||
                ((header >> 7) & 1u) != entry->multifunction)
                fail("dma-live-identity");
            uint16_t command = (uint16_t)pci_config_dword(
                device, function, 0x04);
            if (command != q35_live_pci_snapshot.functions[index].command_after ||
                (command & PCI_COMMAND_BUS_MASTER) != 0 ||
                (command & ~PCI_COMMAND_MODEL_MASK) != 0)
                fail("dma-live-command");
            seen |= 1u << index;
            ++present;
        }
    }
    for (unsigned i = 0;
         i < sizeof(q35_pci_manifest) / sizeof(q35_pci_manifest[0]); ++i) {
        if (!(seen & (1u << i)) && q35_pci_manifest[i].required)
            fail("dma-live-required-missing");
    }
    if (present != 5) fail("dma-live-inventory");
}

#if LEANOS_RETURN_CORRUPTION_MODE == 25
/* Controlled machine negative only: restore the SATA bus-master bit after the
   accepted boot snapshot so the production outbound read-back must reject. */
static __attribute__((noinline, noipa)) void inject_dma_bus_master_reenable(void) {
    pci_config_command(31, 2, (uint16_t)(
        q35_live_pci_snapshot.functions[4].command_after |
        PCI_COMMAND_BUS_MASTER));
}
#endif

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

static __attribute__((noinline, noipa)) uint64_t
replay_composite_or_unknown(const struct oracle_vector *v) {
    if (v->adapter == 18) {
        return leanos_composite_dispatch(
            v->words[0], v->words[1], v->words[2],
            v->words[3], v->words[4], v->words[5]);
    }
    return UINT64_MAX;
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
                        ? leanos_boot_select_frame(v->words[0], v->words[1], v->words[2],
                            v->words[3], v->words[4], v->words[5])
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
                                                    : v->adapter == 13
                                                        ? leanos_direct_port_io_demo(v->words[0],
                                                        v->words[1], v->words[2], v->words[3],
                                                        v->words[4], v->words[5])
                                                        : v->adapter == 14
                                                            ? leanos_nmi_demo(v->words[0],
                                                            v->words[1], v->words[2], v->words[3],
                                                            v->words[4])
                                                            : v->adapter == 15
                                                            ? leanos_boot_phase_demo(v->words[0],
                                                            v->words[1], v->words[2], v->words[3],
                                                            v->words[4])
                                                            : v->adapter == 16
                                                            ? leanos_stale_translation_demo(
                                                            v->words[0], v->words[1], v->words[2],
                                                            v->words[3], v->words[4], v->words[5])
                                                            : v->adapter == 17
                                                            ? leanos_page_fault_demo(v->words[0],
                                                            v->words[1], v->words[2],
                                                            v->words[3], v->words[4])
                                                            : replay_composite_or_unknown(v);
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
    tss.ist[1] = (uint64_t)__nmi_ist_stack_end;
    tss.iomap = sizeof(tss);
#ifdef LEANOS_ENTRY_HIGH_WATER
    initialize_entry_stack_high_water();
#endif
    *(uint64_t *)__df_ist_stack_start = 0xd0b1efa17badc0deull;
    *(uint64_t *)((uint64_t)__df_ist_stack_end - 128u) =
        0x15a1c0decafef00dull;
    *(uint64_t *)__nmi_ist_stack_start = 0x4e4d493253544143ull;
    *(uint64_t *)((uint64_t)__nmi_ist_stack_end - 128u) =
        0x4b5445524d494e41ull;
#ifdef LEANOS_NMI_PROBE
    *(uint64_t *)__entry_stack_start = UINT64_C(0x4f5244494e415259);
    *(uint64_t *)((uint64_t)__entry_stack_end - 128u) =
        UINT64_C(0x535441434b43414e);
#endif
    load_tss();
    set_gate(0, isr0, 0, 0x8e);
    set_gate(2, isr2, 2, 0x8e);
    set_gate(3, isr3, 0, 0xee);
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
    check_direct_port_control(1);
}

#ifdef LEANOS_NMI_PROBE
static int nmi_cpl3_requested(uint32_t magic, uint32_t info_address) {
    if (magic != MULTIBOOT2_RUNTIME_MAGIC || info_address < 8 ||
        info_address >= BOOT_ACCESSIBLE_LIMIT) return 0;
    const uint8_t *info = (const uint8_t *)(uintptr_t)info_address;
    uint32_t total = *(const uint32_t *)info;
    if (total < 16 || total > MAX_HANDOFF_BYTES ||
        total > BOOT_ACCESSIBLE_LIMIT - info_address) return 0;
    for (uint32_t offset = 8; offset + 8 <= total;) {
        const struct mb2_tag *tag = (const struct mb2_tag *)(info + offset);
        if (tag->size < 8 || tag->size > total - offset) return 0;
        if (tag->type == 1) {
            static const char expected[] = "nmi-cpl3";
            if (tag->size != 8 + sizeof(expected)) return 0;
            const char *value = (const char *)(tag + 1);
            unsigned i = 0;
            for (; i < sizeof(expected); ++i)
                if (value[i] != expected[i]) return 0;
            return 1;
        }
        if (tag->type == 0) return 0;
        uint32_t advance = (tag->size + 7u) & ~7u;
        if (advance < tag->size || advance > total - offset) return 0;
        offset += advance;
    }
    return 0;
}
#endif

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
#ifdef LEANOS_ENTRY_ADVERSARIAL
    if (current_subject == 2 && number == 15) {
        check_selected_root_b();
        if (blocking_ipc_step != 2 || entry_adversarial_step != 3 ||
            direct_port_fault_attestation != UINT64_C(0x00000000ff020202) ||
            arg0 != UINT64_C(0xb2b2d13e51a7e55e) ||
            arg1 != UINT64_C(0x030201) || arg2 != UINT64_C(0x51a7))
            fail("direct-port-peer-state");
        serial_puts("LEANOS/16 DIRECT-PORT-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS\n");
        serial_puts("LEANOS/16 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1 device-mutation=0\n");
        finish(0x10);
    }
#endif
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
#ifdef LEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO
    if (number == 16 && current_subject == 2) {
        check_selected_root_b();
        if (arg0 != UINT64_C(0xb2b2d0d151a7e55e) || arg1 != 0x030201 ||
            arg2 != 0x51a7 ||
            direct_port_fault_attestation != UINT64_C(0x00000000ff020202))
            fail("direct-port-peer-state");
        /* Independent hardware oracle for the PIC probe: the survivor triggers
           a kernel-owned read-back of the master 8259 interrupt mask.  It reads
           the actual device register, not the serial claim, so a denied write
           leaves the init value (0xff) intact while an escaped write to 0x21
           would have cleared the mask and this check would fail-stop even under
           a forged "device-mutation=0" transcript. */
        if (direct_port_probe_class == 3) {
            uint8_t observed_pic_mask = in8(0x21);
            if (observed_pic_mask != 0xffu)
                fail("direct-port-pic-canary");
            serial_puts("LEANOS/16 DIRECT-PORT-CANARY register=pic-mask port=33 programmed=255 observed=255 device-mutation=0 result=PASS\n");
        }
        serial_puts("LEANOS/16 DIRECT-PORT-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS\n");
        serial_puts("LEANOS/16 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1 device-mutation=0\n");
        finish(0x10);
    }
#endif
#ifdef LEANOS_INTEGER_FAULT_SCENARIO
    if (number == 17 && current_subject == 2) {
        check_selected_root_b();
        if (arg0 != UINT64_C(0xb2b2de3b51a7e55e) || arg1 != 0x030201 ||
            arg2 != 0x51a7 ||
            integer_fault_attestation != (integer_fault_probe_class == 1
                ? UINT64_C(0x00000200ff020202) : UINT64_C(0x00000100ff020202)))
            fail("integer-fault-peer-state");
        serial_puts(integer_fault_probe_class == 1
            ? "LEANOS/18 BREAKPOINT-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS\n"
            : "LEANOS/18 DIVIDE-ERROR-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS\n");
        serial_puts(integer_fault_probe_class == 1
            ? "LEANOS/18 FINAL status=PASS faulting=terminated survivor=2 vector=3 reason=breakpoint kernel-origin=fail-stop\n"
            : "LEANOS/18 FINAL status=PASS faulting=terminated survivor=2 vector=0 reason=divide-error kernel-origin=fail-stop\n");
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
        arm_timer();
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

__attribute__((noinline))
uint64_t page_fault_handler(const struct page_fault_transition *transition) {
    const struct page_fault_entry_record *snapshot = transition->snapshot;
    const uint64_t error = snapshot->error;
    const uint64_t rip = snapshot->rip;
    const uint64_t fault_address = snapshot->fault_address;
    if (transition->kind != PAGE_FAULT_TRANSITION_CONTAIN)
        fail("page-fault-containment-bypass");
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
    const uint64_t expected_error = page_fault_probe_class == 2 ? 21u :
        page_fault_probe_class == 1 ? 7u : 5u;
    const uint64_t expected_rip = page_fault_probe_class == 2
        ? (uint64_t)user_a_nx_fault_instruction
        : page_fault_probe_class == 1
        ? (uint64_t)user_a_write_fault_instruction
        : (uint64_t)user_a_fault_instruction;
    const uint64_t expected_address = page_fault_probe_class == 2
        ? (uint64_t)user_a_nx_fault_instruction
        : page_fault_probe_class == 1
        ? (uint64_t)user_a_write_target : 0u;
    if (error == expected_error && rip == expected_rip &&
        fault_address == expected_address) {
        if (snapshot->current_subject != 1 ||
            snapshot->active_address_space != 1 ||
            snapshot->active_cr3 != (uint64_t)page_map_level_4_a ||
            saved_context_owner_b != 2 ||
            !initial_b_frame_valid(initial_context_b))
            fail("fault-authority-binding");
        if (page_fault_probe_class == 1) {
            uint8_t write_canary;
            smap_copy_from(&write_canary, user_a_write_target, 1);
            if (write_canary != 0xa5u)
                fail("fault-write-canary");
        } else if (page_fault_probe_class == 2) {
            static const uint8_t expected_payload[9] = {
                0xb8, 0xff, 0x00, 0x00, 0x00, 0xcd, 0x80, 0x0f, 0x0b
            };
            uint8_t payload[9];
            smap_copy_from(payload, user_a_nx_fault_instruction,
                           sizeof(payload));
            for (unsigned i = 0; i < sizeof(payload); ++i)
                if (payload[i] != expected_payload[i])
                    fail("fault-nx-payload");
        }
        uint64_t result = transition->result;
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
        if (page_fault_probe_class == 2) {
            serial_puts("LEANOS/14 FAULT-ENTRY vector=14 error=21 access=execute protection=1 cr2=");
            serial_u64((uint64_t)user_a_nx_fault_instruction);
            serial_puts(" rip=user-a-nx-fault-instruction origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 dispatch=0x00000000ff020202 cleanup=31 survivor=2 payload-canary=armed result=PASS\n");
        } else if (page_fault_probe_class == 1) {
            serial_puts("LEANOS/14 FAULT-ENTRY vector=14 error=7 access=write protection=1 cr2=");
            serial_u64((uint64_t)user_a_write_target);
            serial_puts(" rip=user-a-write-fault-instruction origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 dispatch=0x00000000ff020202 cleanup=31 survivor=2 write-canary=unchanged result=PASS\n");
        } else {
            serial_puts("LEANOS/14 FAULT-ENTRY vector=14 error=5 access=read protection=1 cr2=0 rip=user-a-fault-instruction origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 dispatch=0x00000000ff020202 cleanup=31 survivor=2 result=PASS\n");
        }
        fault_dispatch_attestation = result;
        current_subject = selected;
        serial_puts("LEANOS/14 TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS\n");
        serial_puts("LEANOS/14 DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS\n");
        return 2;
    }
#endif
    if (error != 5u || rip != (uint64_t)user_a_fault_instruction ||
        fault_address != 0u)
        fail("user-fault");
#ifdef LEANOS_ENTRY_HIGH_WATER
    report_entry_stack_high_water("user-page-fault");
#endif
    serial_puts("LEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS\n");
    return (uint64_t)user_a_fault_recovered;
}

__attribute__((noinline))
uint64_t page_fault_diagnostic_handler(
    const struct page_fault_transition *transition) {
    const uint64_t recovery = transition->result &
        UINT64_C(0x0000ffffffffffff);
    const uint64_t completed_state = transition->result >> 48;
    if (transition->kind != PAGE_FAULT_TRANSITION_KERNEL_DIAGNOSTIC ||
        recovery == 0 ||
        (completed_state != 2 && completed_state != 4 &&
         completed_state != 6))
        fail("page-fault-diagnostic-bypass");
    supervisor_probe = (unsigned)completed_state;
    if (completed_state == 2) {
        serial_puts("LEANOS/4 PROBE kind=wp vector=14 error=3 origin=kernel address=kernel-text policy=fatal result=PASS\n");
    } else if (completed_state == 4) {
        serial_puts("LEANOS/4 PROBE kind=smep vector=14 error=17 origin=kernel address=user-a-text policy=fatal result=PASS\n");
    } else {
        serial_puts("LEANOS/6 PROBE kind=smap-direct vector=14 origin=kernel ac=0 result=PASS\n");
    }
    return recovery;
}

/* Construct one immutable vector-14 record before any operation-specific
   handler.  `frame` points at the one preserved CR2 word followed by the
   saved GPR bank and the hardware error/frame.  CR2 is never reread here.
   The generated adapter must agree with the record's architectural fields and
   independently sampled kernel context before page_fault_handler is called. */
__attribute__((noinline))
uint64_t authorize_page_fault_snapshot(const uint64_t *frame) {
    uint64_t cr3, cr0, cr4;
    uint32_t provenance_efer_low, provenance_efer_high;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
    __asm__ volatile (".global page_fault_provenance_efer_read\n"
                      "page_fault_provenance_efer_read:\n"
                      "rdmsr" : "=a"(provenance_efer_low),
                      "=d"(provenance_efer_high)
                      : "c"(UINT32_C(0xc0000080)));
    (void)provenance_efer_high;

    const uint64_t error = frame[16];
    const uint64_t saved_cs = frame[18];
    const uint64_t user = (saved_cs & 3u) == 3u;
    const uint64_t active_address_space =
        cr3 == (uint64_t)page_map_level_4_a ? 1u :
        cr3 == (uint64_t)page_map_level_4_b ? 2u : 0u;
    const uint64_t paging_controls =
        ((cr0 >> 16) & 1u) |
        ((uint64_t)(provenance_efer_low >> 11) & 1u) << 1 |
        ((cr4 >> 20) & 1u) << 2 |
        ((cr4 >> 21) & 1u) << 3;
    const uint64_t trusted_subject = current_subject;
    const uint64_t trusted_stack_identity = user ? 1u : 2u;
    const struct page_fault_entry_record snapshot = {
        .version = 1,
        .vector = 14,
        .error = error,
        .fault_address = frame[0],
        .fault_page = frame[0] >> 12,
        .access = ((error >> 4) & 1u) != 0 ? 2u :
                  ((error >> 1) & 1u) != 0 ? 1u : 0u,
        .protection = error & 1u,
        .user = user,
        .current_subject = trusted_subject,
        .active_address_space = active_address_space,
        .active_cr3 = cr3,
        .paging_controls = paging_controls,
        .rip = frame[17],
        .saved_cs = saved_cs,
        .rflags = frame[19],
        .user_rsp = user ? frame[20] : 0,
        .user_ss = user ? frame[21] : 0,
        .stack_identity = trusted_stack_identity,
        .reserved = 0
    };
    const uint64_t canonical = leanos_authorize_page_fault_snapshot(
        snapshot.version, snapshot.vector, snapshot.error,
        snapshot.fault_address, snapshot.fault_page, snapshot.access,
        snapshot.protection, snapshot.user, snapshot.current_subject,
        snapshot.active_address_space, snapshot.active_cr3,
        snapshot.paging_controls, snapshot.rip, snapshot.saved_cs,
        snapshot.rflags, snapshot.user_rsp, snapshot.user_ss,
        snapshot.stack_identity, snapshot.reserved, trusted_subject,
        active_address_space, cr3, paging_controls, trusted_stack_identity);
    uint64_t *root = active_address_space == 1 ? page_map_level_4_a :
                     active_address_space == 2 ? page_map_level_4_b : 0;
    uint64_t *pdpt = active_address_space == 1 ? page_directory_pointer_a :
                     active_address_space == 2 ? page_directory_pointer_b : 0;
    uint64_t *pd = active_address_space == 1 ? page_directory_a :
                   active_address_space == 2 ? page_directory_b : 0;
    uint64_t *pt = active_address_space == 1 ? page_table_a :
                   active_address_space == 2 ? page_table_b : 0;
    const uint64_t report_agrees = !user ||
        (root != 0 && decoded_root_matches((unsigned)active_address_space,
                                           root, pdpt, pd, pt, 0));
    const uint64_t expected_leaf =
        user && snapshot.fault_page < BOOT_LEAF_COUNT ?
            expected_boot_leaf((unsigned)active_address_space,
                               snapshot.fault_page) : 0;
    const uint64_t live_leaf =
        user && pt != 0 && snapshot.fault_page < BOOT_LEAF_COUNT ?
            pt[snapshot.fault_page] & ~(PTE_ACCESSED | PTE_DIRTY) : 0;
    /* Each admitted production probe binds one reviewed instruction, address,
       architectural error/access class, and the active generated leaf.  The
       immutable snapshot itself selects the exact INVLPG operand; this closes
       the single-core stale-translation assumption before the generated
       agreement transition consumes its live walk. */
    const uint64_t reviewed_fault =
        page_fault_probe_class == 0
            ? user && snapshot.fault_address == 0 &&
              snapshot.fault_page == 0 && snapshot.error == 5 &&
              snapshot.access == 0 && snapshot.protection == 1 &&
              snapshot.rip == (uint64_t)user_a_fault_instruction
            : page_fault_probe_class == 1
            ? user &&
              snapshot.fault_address == (uint64_t)user_a_write_target &&
              snapshot.fault_page ==
                  (uint64_t)user_a_write_target / PAGE_BYTES &&
              snapshot.error == 7 && snapshot.access == 1 &&
              snapshot.protection == 1 &&
              snapshot.rip == (uint64_t)user_a_write_fault_instruction
            : page_fault_probe_class == 2
            ? user &&
              snapshot.fault_address ==
                  (uint64_t)user_a_nx_fault_instruction &&
              snapshot.fault_page ==
                  (uint64_t)user_a_nx_fault_instruction / PAGE_BYTES &&
              snapshot.error == 21 && snapshot.access == 2 &&
              snapshot.protection == 1 &&
              snapshot.rip == (uint64_t)user_a_nx_fault_instruction
            : page_fault_probe_class == 3
            ? user &&
              snapshot.fault_address ==
                  (uint64_t)user_a_nx_fault_instruction &&
              snapshot.fault_page ==
                  (uint64_t)user_a_nx_fault_instruction / PAGE_BYTES &&
              snapshot.error == 12 && snapshot.access == 0 &&
              snapshot.protection == 0 &&
              snapshot.rip == (uint64_t)user_a_reserved_fault_instruction
            : page_fault_probe_class == 4
            ? user && snapshot.fault_address == 0 &&
              snapshot.fault_page == 0 && snapshot.error == 5 &&
              snapshot.access == 0 && snapshot.protection == 1 &&
              snapshot.rip == (uint64_t)user_a_fault_instruction
            : 0;
    const uint64_t exact_fault_page_invalidation =
        invalidate_snapshot_fault_page(&snapshot);
    const uint64_t checked_exact_fault_page_invalidation =
        reviewed_fault && exact_fault_page_invalidation;
    /* The mismatch fixture changes exactly one expected-walk bit.  The
       hardware snapshot, decoded live walk, and all trusted bindings remain
       untouched inputs to the generated #170 policy adapter. */
    const uint64_t policy_expected_leaf = page_fault_probe_class == 4
        ? expected_leaf ^ PTE_WRITABLE : expected_leaf;
    const uint64_t route = leanos_page_fault_dispatch_transition(
        snapshot.version, snapshot.vector, snapshot.error,
        snapshot.fault_address, snapshot.fault_page, snapshot.access,
        snapshot.protection, snapshot.user, snapshot.current_subject,
        snapshot.active_address_space, snapshot.active_cr3,
        snapshot.paging_controls, snapshot.rip, snapshot.saved_cs,
        snapshot.rflags, snapshot.user_rsp, snapshot.user_ss,
        snapshot.stack_identity, snapshot.reserved, trusted_subject,
        active_address_space, cr3, paging_controls, trusted_stack_identity,
        canonical, supervisor_probe,
        (uint64_t)wp_probe_instruction, (uint64_t)wp_probe_target,
        (uint64_t)wp_probe_recovered,
        (uint64_t)user_a_entry, (uint64_t)user_a_entry,
        (uint64_t)smep_probe_recovered,
        (uint64_t)smap_probe_instruction, (uint64_t)user_a_stack,
        (uint64_t)smap_probe_recovered,
        active_address_space, (uint64_t)root,
        active_address_space, (uint64_t)root, report_agrees,
        policy_expected_leaf, live_leaf,
        current_subject == snapshot.current_subject, 1, current_subject,
        active_address_space, active_address_space, active_address_space,
        0, 0, checked_exact_fault_page_invalidation, current_subject,
        active_address_space,
        saved_context_owner_b, saved_context_owner_b);
    const struct page_fault_transition transition = {
        .kind = (enum page_fault_transition_kind)(route >> 56),
        .result = route & UINT64_C(0x00ffffffffffffff),
        .snapshot = &snapshot
    };
    if (snapshot.active_address_space == 0 ||
        snapshot.current_subject != snapshot.active_address_space ||
        (user && page_fault_probe_class == 3
            ? canonical != 0 : canonical == 0))
        fail("page-fault-provenance");
    switch (transition.kind) {
    case PAGE_FAULT_TRANSITION_CONTAIN:
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
        /* The reason-sensitive images publish the canonical evidence record.
           Preserve the ordinary #102 transcript while still routing its
           baseline probe through this same generated production adapter. */
        report_page_fault_snapshot(
            &snapshot, canonical, route, expected_leaf, live_leaf);
#endif
        return page_fault_handler(&transition);
    case PAGE_FAULT_TRANSITION_KERNEL_DIAGNOSTIC:
        return page_fault_diagnostic_handler(&transition);
    case PAGE_FAULT_TRANSITION_FATAL:
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
        if (page_fault_probe_class == 3 || page_fault_probe_class == 4) {
            if (!checked_exact_fault_page_invalidation)
                fail("page-fault-terminal-witness");
            report_page_fault_terminal(
                &snapshot, canonical, route, policy_expected_leaf, live_leaf);
        }
#endif
        fail("page-fault-fatal");
    case PAGE_FAULT_TRANSITION_REJECTED:
    default:
        fail("page-fault-rejected");
    }
}

#ifdef LEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO
/* Trusted machine adapter for the direct-port-containment family.  Subject A
   executed exactly one reviewed raw CPL3 port instruction, so hardware
   delivered #GP(0) before the device operation could take effect.  This
   routine snapshots the live privilege configuration, types the
   state-preserving denial through the generated DirectPortIO adapter (device
   projection unchanged), and then reuses the shared contained-user-fault
   cleanup/dispatch adapter exactly like the page-fault containment scenario.
   The untrusted port/value/direction words are recorded only as diagnostics;
   they cannot select the current subject, the survivor, the kernel purpose, or
   a claim that no side effect occurred. */
uint64_t direct_port_containment_gp_handler(uint64_t error, uint64_t rip,
                                            uint64_t saved_cs, uint64_t saved_rdx,
                                            uint64_t saved_rax) {
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    uint64_t port = saved_rdx & UINT64_C(0xffff);
    uint64_t value = saved_rax & UINT64_C(0xff);
    uint64_t expected_port;
    uint64_t direction_width;
    unsigned check_value;
    uint64_t expected_value;
    if (direct_port_probe_class == 1) {
        expected_port = DEBUG_EXIT; direction_width = 1;
        check_value = 1; expected_value = UINT64_C(0x11);
    } else if (direct_port_probe_class == 2) {
        expected_port = UINT64_C(0x3fd); direction_width = 0;
        check_value = 0; expected_value = 0;
    } else if (direct_port_probe_class == 3) {
        /* Byte OUT of 0x00 to the master PIC data/mask port: an attempt to
           clear the interrupt mask programmed at init.  Denied under the same
           #GP(0) path; the surviving peer's mask read-back is the independent
           oracle. */
        expected_port = UINT64_C(0x21); direction_width = 1;
        check_value = 1; expected_value = 0;
    } else if (direct_port_probe_class == 0) {
        expected_port = COM1; direction_width = 1;
        check_value = 1; expected_value = UINT64_C(0x41);
    } else {
        fail("direct-port-probe-class");
    }
    if (saved_cs != 0x23 || error != 0 ||
        rip != (uint64_t)user_a_direct_port_probe || port != expected_port ||
        (check_value && value != expected_value) ||
        current_subject != 1 || cr3 != (uint64_t)page_map_level_4_a)
        fail("direct-port-gp-binding");
    check_direct_port_control(0);
    /* DirectPortIO types the architectural #GP(0) denial and leaves every
       device projection byte-identical.  The reviewed user origin denies
       independently of the untrusted port/value/direction operands. */
    if (leanos_direct_port_io_demo(0, 0, 0, port, direction_width, value) !=
        UINT64_C(0x0144332211))
        fail("direct-port-model-denial");
    if (saved_context_owner_b != 2 || !initial_b_frame_valid(initial_context_b))
        fail("direct-port-peer-context");
    /* The canonical contained-user-fault class reuses the existing atomic
       cleanup/survivor-dispatch adapter (reason code zero, vector-14 class). */
    uint64_t result = leanos_fault_dispatch_demo(14, saved_cs & 3u,
        current_subject, current_subject, saved_context_owner_b,
        saved_context_owner_b);
    if (result != UINT64_C(0x00000000ff020202))
        fail("direct-port-fault-dispatch");
    uint64_t selected = (result >> 8) & 0xffu;
    uint64_t address_space = (result >> 16) & 0xffu;
    uint64_t cleanup = (result >> 24) & 0x1fu;
    if (selected != saved_context_owner_b || address_space != 2 ||
        cleanup != 0x1fu || ((result >> 29) & 7u) != 7u)
        fail("direct-port-fault-encoding");
    direct_port_fault_attestation = result;
    current_subject = selected;
    serial_puts(direct_port_probe_class == 1
        ? "LEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=244 direction=out width=byte purpose=user device-mutation=0 result=PASS\n"
        : direct_port_probe_class == 2
        ? "LEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=1021 direction=in width=byte purpose=user device-mutation=0 result=PASS\n"
        : direct_port_probe_class == 3
        ? "LEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=33 direction=out width=byte purpose=user device-mutation=0 result=PASS\n"
        : "LEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=1016 direction=out width=byte purpose=user device-mutation=0 result=PASS\n");
    serial_puts("LEANOS/16 DIRECT-PORT-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS\n");
    serial_puts("LEANOS/16 DIRECT-PORT-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS\n");
    return 2;
}
#endif

/* Trusted machine adapters for the real integer divide-error (#DE, vector 0)
   and breakpoint (#BP, vector 3) containment scenarios.  Each is reached only
   through its manifest-checked live IDT gate and the common normalizer; it binds
   the saved-RIP class without using RIP as an authority input, consumes the
   shared generated typed dispatcher (distinct reason code per class), retires A,
   and dispatches B.  isr0/isr3 always link these; the containment logic is only
   built into the shared integer-fault kernel object. */
uint64_t divide_error_handler(uint64_t rip, uint64_t saved_cs) {
#ifdef LEANOS_INTEGER_FAULT_SCENARIO
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if (integer_fault_probe_class != 0 || saved_cs != 0x23 ||
        current_subject != 1 || rip != (uint64_t)user_a_divide_instruction ||
        cr3 != (uint64_t)page_map_level_4_a || saved_context_owner_b != 2 ||
        !initial_b_frame_valid(initial_context_b))
        fail("divide-error-binding");
    serial_puts("LEANOS/18 DIVIDE-ERROR-ENTRY vector=0 error=none origin=cpl3 hardware=1 direct-call=0 saved-rip=faulting-instruction subject=1 address-space=1 result=PASS\n");
    uint64_t result = leanos_fault_dispatch_demo(0, saved_cs & 3u,
        current_subject, current_subject, saved_context_owner_b,
        saved_context_owner_b);
    if (result != UINT64_C(0x00000100ff020202))
        fail("divide-error-dispatch");
    uint64_t selected = (result >> 8) & 0xffu;
    uint64_t address_space = (result >> 16) & 0xffu;
    uint64_t cleanup = (result >> 24) & 0x1fu;
    uint64_t reason = (result >> 40) & 0xffu;
    if (selected != saved_context_owner_b || address_space != 2 ||
        cleanup != 0x1fu || ((result >> 29) & 7u) != 7u || reason != 1)
        fail("divide-error-encoding");
    integer_fault_attestation = result;
    current_subject = selected;
    serial_puts("LEANOS/18 DIVIDE-ERROR-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS\n");
    serial_puts("LEANOS/18 DIVIDE-ERROR-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned reason=divide-error result=PASS\n");
    return 0;
#else
    (void)rip;
    (void)saved_cs;
    fail("divide-error-unexpected");
#endif
}

uint64_t breakpoint_handler(uint64_t rip, uint64_t saved_cs) {
#ifdef LEANOS_INTEGER_FAULT_SCENARIO
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if (integer_fault_probe_class != 1 || saved_cs != 0x23 ||
        current_subject != 1 || rip != (uint64_t)user_a_breakpoint_after ||
        cr3 != (uint64_t)page_map_level_4_a || saved_context_owner_b != 2 ||
        !initial_b_frame_valid(initial_context_b))
        fail("breakpoint-binding");
    serial_puts("LEANOS/18 BREAKPOINT-ENTRY vector=3 error=none origin=cpl3 hardware=1 direct-call=0 saved-rip=post-instruction subject=1 address-space=1 result=PASS\n");
    uint64_t result = leanos_fault_dispatch_demo(3, saved_cs & 3u,
        current_subject, current_subject, saved_context_owner_b,
        saved_context_owner_b);
    if (result != UINT64_C(0x00000200ff020202))
        fail("breakpoint-dispatch");
    uint64_t selected = (result >> 8) & 0xffu;
    uint64_t address_space = (result >> 16) & 0xffu;
    uint64_t cleanup = (result >> 24) & 0x1fu;
    uint64_t reason = (result >> 40) & 0xffu;
    if (selected != saved_context_owner_b || address_space != 2 ||
        cleanup != 0x1fu || ((result >> 29) & 7u) != 7u || reason != 2)
        fail("breakpoint-encoding");
    integer_fault_attestation = result;
    current_subject = selected;
    serial_puts("LEANOS/18 BREAKPOINT-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS\n");
    serial_puts("LEANOS/18 BREAKPOINT-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned reason=breakpoint result=PASS\n");
    return 0;
#else
    (void)rip;
    (void)saved_cs;
    fail("breakpoint-unexpected");
#endif
}

/* The sole boot-reachable Lean runtime primitive. See docs/boot-image.md. */
uint8_t lean_uint64_dec_eq(uint64_t left, uint64_t right) {
    return (uint8_t)(left == right);
}

void kernel_main(uint32_t multiboot_magic, uint32_t multiboot_info) {
    serial_init();
#ifdef LEANOS_NMI_PROBE
    int nmi_cpl3 = nmi_cpl3_requested(multiboot_magic, multiboot_info);
    serial_puts("LEANOS/17 BOOT target=x86_64-q35 schedule=nmi-terminal-probe controls=idt2,ist2,nmi\n");
#elif defined(LEANOS_EXTENDED_STATE_SCENARIO)
    serial_puts(extended_state_probe_class >= 5
        ? "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fast-entry-denial controls=wp,smep,smap,em,mp,ts,sce-off\n"
        : "LEANOS/13 BOOT target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts\n");
#elif defined(LEANOS_FAULT_CONTAINMENT_SCENARIO)
    serial_puts(page_fault_probe_class == 4
        ? "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-integrity probe=walk-mismatch contract=v1 controls=wp,smep,smap\n"
        : page_fault_probe_class == 3
        ? "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-integrity probe=reserved-bit contract=v1 controls=wp,smep,smap\n"
        : page_fault_probe_class == 2
        ? "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment probe=nx-execute contract=v1 controls=wp,smep,smap\n"
        : page_fault_probe_class == 1
        ? "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment probe=readonly-write contract=v1 controls=wp,smep,smap\n"
        : "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment probe=supervisor-read contract=v1 controls=wp,smep,smap\n");
#elif defined(LEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO)
    serial_puts(direct_port_probe_class == 1
        ? "LEANOS/16 BOOT target=x86_64-q35 subjects=2 schedule=direct-port-containment probe=debug-exit contract=v1 controls=wp,smep,smap\n"
        : direct_port_probe_class == 2
        ? "LEANOS/16 BOOT target=x86_64-q35 subjects=2 schedule=direct-port-containment probe=serial-in contract=v1 controls=wp,smep,smap\n"
        : direct_port_probe_class == 3
        ? "LEANOS/16 BOOT target=x86_64-q35 subjects=2 schedule=direct-port-containment probe=pic-mask contract=v1 controls=wp,smep,smap\n"
        : "LEANOS/16 BOOT target=x86_64-q35 subjects=2 schedule=direct-port-containment probe=serial-out contract=v1 controls=wp,smep,smap\n");
#elif defined(LEANOS_INTEGER_FAULT_SCENARIO)
    serial_puts(integer_fault_probe_class == 1
        ? "LEANOS/18 BOOT target=x86_64-q35 subjects=2 schedule=integer-fault-containment probe=breakpoint contract=v1 controls=wp,smep,smap\n"
        : "LEANOS/18 BOOT target=x86_64-q35 subjects=2 schedule=integer-fault-containment probe=divide-error contract=v1 controls=wp,smep,smap\n");
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
#ifdef LEANOS_NMI_PROBE
    /* Model an NMI selected between composite steps while the ordinary-entry
       mode is handling.  IF remains clear: QEMU's monitor-injected NMI must
       cross the interrupt mask and use the dedicated IST2 gate. */
    if (!nmi_cpl3) {
        ordinary_entry_active = 1;
        serial_puts("LEANOS/17 NMI-READY origin=cpl0 prior=handling if=0 gate=2 ist=2 subject=1 address-space=1 purpose=syscall canaries=armed result=PASS\n");
        for (;;) __asm__ volatile ("cli; hlt");
    }
#endif
    check_fast_entry_cpuid();
    check_fast_entry_control();
#ifdef LEANOS_NMI_PROBE
#elif defined(LEANOS_EXTENDED_STATE_SCENARIO)
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
#ifdef LEANOS_NMI_PROBE
    current_subject = 1;
    activate_user_address_space(page_map_level_4_a);
    check_selected_root_a();
    serial_puts("LEANOS/17 NMI-READY origin=cpl3 prior=running if=1 gate=2 ist=2 subject=1 address-space=1 purpose=user-spin canaries=armed result=PASS\n");
    enter_user(user_a_entry, user_a_stack_top);
#elif defined(LEANOS_EXTENDED_STATE_SCENARIO)
    current_subject = 1;
    activate_user_address_space(page_map_level_4_a);
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
    activate_user_address_space(page_map_level_4_a);
    check_selected_root_a();
#ifdef LEANOS_PAGE_FAULT_PROBE_RESERVED_BIT
    {
        const uint64_t page =
            (uint64_t)user_a_nx_fault_instruction / PAGE_BYTES;
        /* TCG does not consistently raise RSVD for address bits above its
           configured MAXPHYADDR.  Use the other architectural reserved-leaf
           condition instead: remove NX from every active A leaf, clear
           EFER.NXE, then retain NX only on the target leaf.  Any access through
           that PTE must therefore raise a real vector-14 RSVD violation. */
        for (unsigned i = 0; i < BOOT_LEAF_COUNT; ++i)
            page_table_a[i] &= ~PTE_NX;
        disable_nxe_for_reserved_fault();
        reserved_fault_nxe_disabled = 1;
        page_table_a[page] |= PTE_NX;
        __asm__ volatile ("invlpg (%0)" :
                          : "r"(user_a_nx_fault_instruction) : "memory");
    }
#endif
    serial_puts(page_fault_probe_class >= 3
        ? "LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned fatal-only=1\n"
        : "LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned\n");
    enter_user(user_a_entry, user_a_stack_top);
#elif defined(LEANOS_DIRECT_PORT_CONTAINMENT_SCENARIO)
    current_subject = 1;
    activate_user_address_space(page_map_level_4_a);
    check_selected_root_a();
    serial_puts("LEANOS/16 ENTER subject=1 address-space=1 cpl=3 resources=owned\n");
    enter_user(user_a_entry, user_a_stack_top);
#elif defined(LEANOS_INTEGER_FAULT_SCENARIO)
    current_subject = 1;
    activate_user_address_space(page_map_level_4_a);
    check_selected_root_a();
    serial_puts("LEANOS/18 ENTER subject=1 address-space=1 cpl=3 resources=owned\n");
    enter_user(user_a_entry, user_a_stack_top);
#elif defined(LEANOS_PREEMPTION_SCENARIO)
    enter_user(user_a_entry, user_a_stack_top);
#else
    current_subject = 2;
    activate_user_address_space(page_map_level_4_b);
    check_selected_root_b();
    serial_puts("LEANOS/10 IPC event=enter subject=2 address-space=2 cpl=3 endpoint=10\n");
    enter_user(user_b_entry, user_b_stack_top);
#endif
    fail("iret-returned");
}
