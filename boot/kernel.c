#include <stdint.h>
#include "corpus.h"
#include "generated-boundary-abi.h"
#include "leanos/composite-dispatcher.h"

/* GCC's noipa also blocks interprocedural transformations beyond noinline.
   Clang has no noipa spelling; optnone is the reviewed stronger boundary for
   this independent compiler lane while the shared GNU linker remains in use. */
#if defined(__clang__)
#define noipa optnone
#endif
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
#define PCI_COMMAND_MEMORY (1u << 1)
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
extern uint64_t leanos_boot_machine_acpi_copy_stream_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_acpi_copy_sequence_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_madt_envelope_byte_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t);
extern uint64_t leanos_boot_machine_madt_entry_stream_byte_step_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_machine_topology_admission_result_query(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_init_v5(uint64_t, uint64_t, uint64_t,
                                           uint64_t, uint64_t);
extern uint64_t leanos_boot_decode_step_v5(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_projection_entry(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_projection_manifest(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_projection_free(uint64_t, uint64_t, uint64_t);
#define LEANOS_U64_8 \
    uint64_t, uint64_t, uint64_t, uint64_t, \
    uint64_t, uint64_t, uint64_t, uint64_t
#define LEANOS_U64_64 \
    LEANOS_U64_8, LEANOS_U64_8, LEANOS_U64_8, LEANOS_U64_8, \
    LEANOS_U64_8, LEANOS_U64_8, LEANOS_U64_8, LEANOS_U64_8
extern uint64_t leanos_boot_projection_finish(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t,
    LEANOS_U64_64);
#undef LEANOS_U64_64
#undef LEANOS_U64_8
extern uint64_t leanos_boot_manifest_candidate(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_manifest_start(
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
    uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_consume_exact_projection(uint64_t, uint64_t, uint64_t,
                                        uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_publish_authority(uint64_t, uint64_t, uint64_t,
                                               uint64_t, uint64_t, uint64_t,
                                               uint64_t);
extern uint64_t leanos_boot_authority_result(uint64_t, uint64_t, uint64_t,
                                              uint64_t, uint64_t, uint64_t,
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
extern uint64_t leanos_nmi_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                uint64_t);
extern uint64_t leanos_boot_phase_demo(uint64_t, uint64_t, uint64_t, uint64_t,
                                       uint64_t);
extern uint64_t leanos_stale_translation_demo(uint64_t, uint64_t, uint64_t,
                                              uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_iotlb_publication_demo(uint64_t, uint64_t, uint64_t,
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
#ifdef LEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION
extern char user_b_stale_translation_fault_instruction[];
#endif
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
extern char __vtd_mmio_window_start[], __vtd_mmio_window_end[];
extern char __edu_mmio_window_start[], __edu_mmio_window_end[];
extern uint64_t vtd_root_table[], vtd_context_table[];
extern uint64_t vtd_second_level_root[], vtd_second_level_directory[];
extern uint64_t vtd_second_level_table[];
extern uint64_t vtd_assigned_guard_before[], vtd_assigned_read_buffer[];
extern uint64_t vtd_assigned_write_buffer[], vtd_assigned_guard_after[];

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

/* boot.S consumes this link-visible constant before entering long mode so the
   dedicated image, and only that image, installs the generated EDU BAR leaf. */
#if defined(LEANOS_ASSIGNED_EDU_SCENARIO) && \
    !defined(LEANOS_ASSIGNED_EDU_OMIT_MMIO_MAPPING_FIXTURE)
const uint32_t leanos_assigned_edu_enabled = 1;
#else
const uint32_t leanos_assigned_edu_enabled = 0;
#endif

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
struct boot_projection_entry { uint64_t base, length, kind; };
static struct boot_projection_entry boot_projection_entries[256];
static uint64_t boot_projection_usable[64];
static uint64_t boot_projection_blocked[64];
static uint64_t boot_projection_reserved[64];
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
/* Page 7 is deliberately outside the linked boot image.  These two
   image-reserved frames back its bounded runtime-mutable mapping window. */
static uint64_t runtime_mapping_frame_before[PAGE_BYTES / sizeof(uint64_t)]
    __attribute__((used, aligned(PAGE_BYTES)));
static uint64_t runtime_mapping_frame_after[PAGE_BYTES / sizeof(uint64_t)]
    __attribute__((used, aligned(PAGE_BYTES)));
static volatile uint64_t runtime_invlpg_publication;
static volatile uint64_t runtime_cr3_publication;
static volatile uint64_t runtime_reuse_publication;
static volatile uint64_t runtime_reuse_owner;
static volatile uint64_t runtime_reuse_lifetime;
#define RUNTIME_MAPPING_PAGE 7u
#define RUNTIME_MAPPING_ADDRESS (RUNTIME_MAPPING_PAGE * PAGE_BYTES)
#define RUNTIME_MAPPING_BEFORE UINT64_C(0x126bef0e)
#define RUNTIME_MAPPING_AFTER UINT64_C(0x126a57e2)
#define RUNTIME_REUSE_MODEL_REPLY UINT64_C(0x200000000)
#define RUNTIME_MAPPING_STATE_BOOT 0u
#define RUNTIME_MAPPING_STATE_BEFORE 1u
#define RUNTIME_MAPPING_STATE_UNMAPPED 2u
#define RUNTIME_MAPPING_STATE_AFTER 3u
#define RUNTIME_MAPPING_STATE_REUSED 4u
static volatile unsigned runtime_mapping_state = RUNTIME_MAPPING_STATE_BOOT;
static unsigned preemption_step;
uint64_t current_subject = 1;
volatile uint64_t reserved_fault_nxe_disabled;

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
#ifdef LEANOS_FRAME_BUDGET_SCENARIO
/* C retains the canonical dispatcher token plus the generated decoder's
   physical-frame result and the generated publication page. Quota, usage,
   allocation, identity, mapping, and cleanup policy remain in Lean. */
static uint64_t frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_INITIAL;
static volatile uint64_t frame_budget_retirement_completion;
/* The boot object remains published on its own frame.  The scenario uses the
   next independently decoded eligible frame and tracks its one live
   publication across A's retirement and B's fresh lifetime. */
static uint64_t frame_budget_boot_published_frame = UINT64_MAX;
static uint64_t frame_budget_physical_frame = UINT64_MAX;
static volatile unsigned frame_budget_publication_live;
static uint64_t frame_budget_rescanned_frame = UINT64_MAX;
static uint64_t frame_budget_rescan_status;
static uint64_t frame_budget_rescan_usable;
static uint64_t frame_budget_rescan_blocked;
static uint64_t frame_budget_rescan_manifest;
static uint64_t frame_budget_user_page = UINT64_MAX;
#endif
#ifdef LEANOS_FAULT_CONTAINMENT_SCENARIO
/* Exact generated-adapter result retained across the checked peer restore.
   This is an attestation, not a second mutable scheduler/lifecycle projection. */
static uint64_t fault_dispatch_attestation;
#endif
static __attribute__((noreturn)) void finish(uint8_t value);
static __attribute__((noreturn)) void fail(const char *reason);
static void serial_puts(const char *text);
static __attribute__((noinline)) void serial_putc(char value);
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
    if (reserved_fault_nxe_disabled)
        efer_denied &= ~(1ull << 11);
    if ((state[0] & efer_model_mask) != efer_denied)
        fail("fast-entry-efer-readback");
    for (unsigned i = 1; i < 8; ++i)
        if (state[i] != 0) fail("fast-entry-target-readback");
}

/* Read the descriptor selected by the live task register rather than trusting
   only the C initializer.  x86 keeps hidden descriptor state after LTR, which
   is part of the documented machine-semantics assumption; STR plus SGDT bind
   the selected descriptor and the stored TSS image that can be reloaded. */
static __attribute__((noinline, noipa)) void check_direct_port_control(unsigned report) {
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

static uint64_t runtime_mapping_leaf(uint64_t *frame) {
    return (uint64_t)frame | PTE_PRESENT | PTE_WRITABLE | PTE_USER | PTE_NX;
}

/* Every leaf remains equal to the generated boot plan except the bounded
   page-7 reuse window.  B/page 7 is the old mapping and A/page 7 becomes the
   fresh-owner mapping only in the reused phase.  Each has one exact value for
   every kernel-owned phase; an unknown phase is never accepted.
   Accessed/dirty bits are ignored only by the caller's ordinary x86
   comparison, just as for immutable leaves. */
static __attribute__((noinline)) int checked_runtime_leaf(
    unsigned space, uint64_t page, uint64_t *expected) {
    if (page != RUNTIME_MAPPING_PAGE || (space != 1 && space != 2))
        return 1;
    if (space == 1) {
        switch (runtime_mapping_state) {
        case RUNTIME_MAPPING_STATE_BOOT:
        case RUNTIME_MAPPING_STATE_BEFORE:
        case RUNTIME_MAPPING_STATE_UNMAPPED:
        case RUNTIME_MAPPING_STATE_AFTER:
            return 1;
        case RUNTIME_MAPPING_STATE_REUSED:
            *expected = runtime_mapping_leaf(runtime_mapping_frame_before);
            return 1;
        default:
            return 0;
        }
    }
    switch (runtime_mapping_state) {
    case RUNTIME_MAPPING_STATE_BOOT:
        return 1;
    case RUNTIME_MAPPING_STATE_BEFORE:
        *expected = runtime_mapping_leaf(runtime_mapping_frame_before);
        return 1;
    case RUNTIME_MAPPING_STATE_UNMAPPED:
        *expected = 0;
        return 1;
    case RUNTIME_MAPPING_STATE_REUSED:
        *expected = 0;
        return 1;
    case RUNTIME_MAPPING_STATE_AFTER:
        *expected = runtime_mapping_leaf(runtime_mapping_frame_after);
        return 1;
    default:
        return 0;
    }
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
        int relation_defined = checked_runtime_leaf(space, page, &expected);
        if (!relation_defined ||
            (actual & ~(PTE_ACCESSED | PTE_DIRTY)) != expected) {
            if (report_mismatch) {
                serial_puts("LEANOS/8 PAGING mismatch root="); serial_u64(space);
                serial_puts(" page="); serial_u64(page);
                serial_puts(" expected="); serial_u64(expected);
                serial_puts(" actual="); serial_u64(actual);
                serial_puts(" mutable-state=");
                serial_u64(runtime_mapping_state);
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

static void expect_runtime_relation_rejected(const char *fixture,
        unsigned state, uint64_t replacement, uint64_t expected) {
    uint64_t saved_leaf = page_table_b[RUNTIME_MAPPING_PAGE];
    unsigned saved_state = runtime_mapping_state;
    page_table_b[RUNTIME_MAPPING_PAGE] = replacement;
    runtime_mapping_state = state;
    __asm__ volatile ("" ::: "memory");
    int accepted = decoded_root_matches(2, page_map_level_4_b,
        page_directory_pointer_b, page_directory_b, page_table_b, 0);
    page_table_b[RUNTIME_MAPPING_PAGE] = saved_leaf;
    runtime_mapping_state = saved_state;
    __asm__ volatile ("" ::: "memory");
    if (accepted) fail("pt-runtime-relation-accepted");
    serial_puts("LEANOS/8 PAGING fixture="); serial_puts(fixture);
    serial_puts(" root=B level=pt page="); serial_u64(RUNTIME_MAPPING_PAGE);
    serial_puts(" expected="); serial_u64(expected);
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
    uint64_t vtd_window = boot_page(__vtd_mmio_window_start);
    expect_live_mutation_rejected("mmio-wrong-frame", &page_table_b[vtd_window],
        vtd_window * PAGE_BYTES | PTE_PRESENT | PTE_WRITABLE | PTE_NX,
        "pt", vtd_window);
    expect_live_mutation_rejected("mmio-flip-user", &page_table_b[vtd_window],
        page_table_b[vtd_window] ^ PTE_USER, "pt", vtd_window);
    expect_runtime_relation_rejected("mutable-wrong-frame",
        RUNTIME_MAPPING_STATE_BEFORE,
        runtime_mapping_leaf(runtime_mapping_frame_after),
        runtime_mapping_leaf(runtime_mapping_frame_before));
    expect_runtime_relation_rejected("mutable-publish-before-invalidation",
        RUNTIME_MAPPING_STATE_UNMAPPED,
        runtime_mapping_leaf(runtime_mapping_frame_before), 0);
    expect_runtime_relation_rejected("mutable-unknown-state", 99u,
        page_table_b[RUNTIME_MAPPING_PAGE],
        expected_boot_leaf(2, RUNTIME_MAPPING_PAGE));

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

static void require_runtime_mapping_relation(const char *reason) {
    if (!decoded_root_matches(1, page_map_level_4_a,
                              page_directory_pointer_a, page_directory_a,
                              page_table_a, 0) ||
        !decoded_root_matches(2, page_map_level_4_b,
                              page_directory_pointer_b, page_directory_b,
                              page_table_b, 0))
        fail(reason);
}

/* This is the active-root implementation of the canonical page(2, 7)
   machine effect.  The volatile PTE store, compiler memory boundary, INVLPG,
   and publication store make the required order visible in the final ELF. */
__attribute__((noinline, used))
static void runtime_unmap_page7_invlpg(uint64_t canonical_reply) {
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if (canonical_reply != LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED ||
        (cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_b)
        fail("runtime-invlpg-authority");
    ((volatile uint64_t *)page_table_b)[RUNTIME_MAPPING_PAGE] = 0;
    __asm__ volatile ("" ::: "memory");
    __asm__ volatile ("invlpg (%0)" :
                      : "r"((uint64_t)RUNTIME_MAPPING_ADDRESS) : "memory");
    if (page_table_b[RUNTIME_MAPPING_PAGE] != 0)
        fail("runtime-invlpg-pte");
    runtime_mapping_state = RUNTIME_MAPPING_STATE_UNMAPPED;
    require_runtime_mapping_relation("runtime-invlpg-relation");
    runtime_invlpg_publication = canonical_reply;
}

/* This is the inactive-root implementation of the same effect.  Selecting
   the exact derived B root after the PTE store supplies the no-PCID CR3 flush;
   completion is published only after a checked CR3 readback. */
__attribute__((noinline, used))
static void runtime_unmap_page7_cr3(uint64_t canonical_reply) {
    uint64_t cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if (canonical_reply != LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED ||
        (cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_a)
        fail("runtime-cr3-authority");
    ((volatile uint64_t *)page_table_b)[RUNTIME_MAPPING_PAGE] = 0;
    __asm__ volatile ("" ::: "memory");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_b) : "memory");
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if ((cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_b ||
        page_table_b[RUNTIME_MAPPING_PAGE] != 0)
        fail("runtime-cr3-completion");
    runtime_mapping_state = RUNTIME_MAPPING_STATE_UNMAPPED;
    require_runtime_mapping_relation("runtime-cr3-relation");
    runtime_cr3_publication = canonical_reply;
}

/* Reuse the exact physical frame that backed B/page 7.  The generated
   post-reuse fixture must say that the old page stays absent.  Only after the
   accepted unmap has been published do we scrub the frame, establish its new
   lifetime/owner, write the replacement canary, map the exact frame into
   A/page 7, recheck both complete live roots, and publish reuse.  All stores
   are volatile so this sequence remains inspectable in the final machine
   image. */
__attribute__((noinline, used))
static void runtime_reuse_page7_frame(uint64_t canonical_reply) {
    const uint64_t model_reply =
        leanos_stale_translation_demo(0, 0, 1, RUNTIME_MAPPING_PAGE, 0, 1);
    volatile uint64_t *frame = runtime_mapping_frame_before;

    if (canonical_reply != LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED ||
        runtime_invlpg_publication != canonical_reply ||
        runtime_mapping_state != RUNTIME_MAPPING_STATE_UNMAPPED ||
        page_table_b[RUNTIME_MAPPING_PAGE] != 0 ||
        model_reply != RUNTIME_REUSE_MODEL_REPLY ||
        runtime_reuse_publication != 0 ||
        runtime_reuse_owner != 0 || runtime_reuse_lifetime != 0)
        fail("runtime-reuse-authority");
    for (unsigned i = 0; i < PAGE_BYTES / sizeof(uint64_t); ++i)
        frame[i] = 0;
    __asm__ volatile ("" ::: "memory");
    runtime_reuse_lifetime = 2;
    runtime_reuse_owner = 1;
    frame[0] = RUNTIME_MAPPING_AFTER;
    __asm__ volatile ("" ::: "memory");
    ((volatile uint64_t *)page_table_a)[RUNTIME_MAPPING_PAGE] =
        runtime_mapping_leaf(runtime_mapping_frame_before);
    __asm__ volatile ("" ::: "memory");
    runtime_mapping_state = RUNTIME_MAPPING_STATE_REUSED;
    require_runtime_mapping_relation("runtime-reuse-relation");
    if (page_table_b[RUNTIME_MAPPING_PAGE] != 0 ||
        (page_table_a[RUNTIME_MAPPING_PAGE] &
         ~(PTE_ACCESSED | PTE_DIRTY)) !=
            runtime_mapping_leaf(runtime_mapping_frame_before) ||
        frame[0] != RUNTIME_MAPPING_AFTER)
        fail("runtime-reuse-binding");
    runtime_reuse_publication = model_reply;
}

/* Exercise both machine spellings against real page tables.  The generated
   composite dispatcher is the sole authority for the effect; C only checks
   its closed typed reply and applies the fixed address-space-2/page-7 target.
   Restoring the boot leaf confines the mutable window to this bounded check. */
static void check_runtime_mapping_invalidation(void) {
    volatile uint64_t *window =
        (volatile uint64_t *)(uint64_t)RUNTIME_MAPPING_ADDRESS;
    const uint64_t canonical_reply = leanos_composite_dispatch(
        LEANOS_COMPOSITE_STATE_DIRECT_MAPPED,
        LEANOS_COMPOSITE_COMMAND_ACCEPTED_SYSCALL_UNMAP,
        RUNTIME_MAPPING_PAGE, 0, 0, 0);
    const uint64_t boot_leaf = expected_boot_leaf(2, RUNTIME_MAPPING_PAGE);

    if (canonical_reply != LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED)
        fail("runtime-unmap-dispatch");
    runtime_mapping_frame_before[0] = RUNTIME_MAPPING_BEFORE;
    runtime_mapping_frame_after[0] = RUNTIME_MAPPING_AFTER;

    page_table_b[RUNTIME_MAPPING_PAGE] =
        runtime_mapping_leaf(runtime_mapping_frame_before);
    runtime_mapping_state = RUNTIME_MAPPING_STATE_BEFORE;
    require_runtime_mapping_relation("runtime-invlpg-before-relation");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_b) : "memory");
    if (*window != RUNTIME_MAPPING_BEFORE)
        fail("runtime-invlpg-before");
    runtime_unmap_page7_invlpg(canonical_reply);
    page_table_b[RUNTIME_MAPPING_PAGE] =
        runtime_mapping_leaf(runtime_mapping_frame_after);
    runtime_mapping_state = RUNTIME_MAPPING_STATE_AFTER;
    require_runtime_mapping_relation("runtime-invlpg-after-relation");
    __asm__ volatile ("" ::: "memory");
    if (*window != RUNTIME_MAPPING_AFTER ||
        runtime_invlpg_publication != canonical_reply)
        fail("runtime-invlpg-reuse");
    serial_puts("LEANOS/19 TLB path=invlpg address-space=2 page=7 pte=cleared order=store,invlpg,publish before=309063438 after=308959202 result=PASS\n");

    page_table_b[RUNTIME_MAPPING_PAGE] =
        runtime_mapping_leaf(runtime_mapping_frame_before);
    runtime_mapping_state = RUNTIME_MAPPING_STATE_BEFORE;
    require_runtime_mapping_relation("runtime-cr3-before-relation");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_b) : "memory");
    if (*window != RUNTIME_MAPPING_BEFORE)
        fail("runtime-cr3-before");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_a) : "memory");
    runtime_unmap_page7_cr3(canonical_reply);
    page_table_b[RUNTIME_MAPPING_PAGE] =
        runtime_mapping_leaf(runtime_mapping_frame_after);
    runtime_mapping_state = RUNTIME_MAPPING_STATE_AFTER;
    require_runtime_mapping_relation("runtime-cr3-after-relation");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_b) : "memory");
    if (*window != RUNTIME_MAPPING_AFTER ||
        runtime_cr3_publication != canonical_reply)
        fail("runtime-cr3-reuse");
    serial_puts("LEANOS/19 TLB path=cr3 address-space=2 page=7 pte=cleared order=store,cr3,publish before=309063438 after=308959202 result=PASS\n");

    page_table_b[RUNTIME_MAPPING_PAGE] = boot_leaf;
    runtime_mapping_state = RUNTIME_MAPPING_STATE_BOOT;
    require_runtime_mapping_relation("runtime-window-restore-relation");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_a) : "memory");
    if (page_table_b[RUNTIME_MAPPING_PAGE] != boot_leaf)
        fail("runtime-window-restore");
    serial_puts("LEANOS/19 TLB authority=generated-composite effect=page address-space=2 page=7 window=restored result=PASS\n");
    serial_puts("LEANOS/19 TLB mutable-leaf=checked address-space=2 page=7 states=boot,before,unmapped,after immutable-leaves=exact result=PASS\n");
}

#ifdef LEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION
static void arm_cpl3_stale_translation_probe(void) {
    runtime_mapping_frame_before[0] = RUNTIME_MAPPING_BEFORE;
    page_table_b[RUNTIME_MAPPING_PAGE] =
        runtime_mapping_leaf(runtime_mapping_frame_before);
    runtime_mapping_state = RUNTIME_MAPPING_STATE_BEFORE;
    require_runtime_mapping_relation("stale-translation-arm-relation");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_b) : "memory");
    if (page_table_b[RUNTIME_MAPPING_PAGE] !=
            runtime_mapping_leaf(runtime_mapping_frame_before))
        fail("stale-translation-arm-leaf");
}
#endif

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
static void verify_vtd_state(void);
#if LEANOS_RETURN_CORRUPTION_MODE == 25
static __attribute__((noinline, noipa)) void inject_dma_bus_master_reenable(void);
#endif
#if LEANOS_RETURN_CORRUPTION_MODE == 26
static __attribute__((noinline, noipa)) void inject_vtd_translation_disable(void);
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
#if LEANOS_RETURN_CORRUPTION_MODE == 26
    case 26: return "vtd-translation-disable";
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
    serial_puts(mode >= 14 && mode <= 26
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
#if LEANOS_RETURN_CORRUPTION_MODE == 26
    case 26:
        inject_vtd_translation_disable();
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
    verify_vtd_state();
    /* Accepted ordinary entries remain armed through handler dispatch and
       context selection.  Clear only in this final validated return gate;
       initial boot dispatch is intentionally unarmed. */
    if (ordinary_entry_active) ordinary_entry_active = 0;
}

static __attribute__((noreturn)) void handoff_fail(const char *reason) {
    serial_puts("LEANOS/7 BOOTALLOC status=FAIL reason="); serial_puts(reason);
    serial_putc('\n'); finish(0x11);
}

struct copied_boot_handoff {
    const uint8_t *bytes;
    uint32_t length;
    uint32_t executing_apic_id;
};

#define MAX_COPIED_ACPI_SDT_BYTES UINT32_C(65536)
#define MAX_ACPI_ROOT_ENTRIES UINT32_C(256)
#define MAX_COPIED_ACPI_TABLE_BYTES (UINT32_C(1024) * UINT32_C(1024))

struct copied_acpi_sdt {
    uint64_t physical_address;
    const uint8_t *bytes;
    uint32_t length;
    uint32_t next_copy_offset;
};

struct acpi_root_entries {
    const uint8_t *bytes;
    uint32_t count;
    uint32_t width;
};

static uint8_t boot_acpi_root_copy[MAX_COPIED_ACPI_SDT_BYTES]
    __attribute__((aligned(8)));
static uint8_t boot_acpi_table_copy[MAX_COPIED_ACPI_TABLE_BYTES]
    __attribute__((aligned(8)));
static struct copied_acpi_sdt boot_acpi_table_copies[MAX_ACPI_ROOT_ENTRIES];
static uint8_t boot_acpi_mapping_window[PAGE_BYTES]
    __attribute__((aligned(PAGE_BYTES)));

/* The ordinary boot identity map intentionally ends at 16 MiB, while q35 may
   place its ACPI SDTs above that boundary.  Copy through one supervisor-only,
   NX aperture in the active boot address space and restore its exact original
   leaf before returning.  Physical-address translation, PTE mutation, TLB
   invalidation, and the byte copy remain an explicit trusted boot boundary;
   generated code still validates every copied byte and all table structure. */
static void copy_acpi_physical_bytes(
        uint64_t physical_address, uint8_t *destination, uint32_t length) {
    const uint64_t physical_limit = UINT64_C(1) << 32;
    const uintptr_t window = (uintptr_t)boot_acpi_mapping_window;
    if (length == 0 || physical_address >= physical_limit ||
        (uint64_t)length > physical_limit - physical_address ||
        (window & (PAGE_BYTES - 1u)) != 0 ||
        window >= BOOT_ACCESSIBLE_LIMIT)
        handoff_fail("topology-sdt-address");
    const uint32_t window_page = (uint32_t)(window / PAGE_BYTES);
    if (window_page >= BOOT_LEAF_COUNT)
        handoff_fail("topology-sdt-window");
    uint64_t active_root;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(active_root));
    if ((active_root & ~(uint64_t)(PAGE_BYTES - 1u)) !=
        (uint64_t)page_map_level_4_a)
        handoff_fail("topology-sdt-address-space");
    const uint64_t saved_leaf = page_table_a[window_page];
    if ((saved_leaf & PTE_PRESENT) == 0 || (saved_leaf & PTE_USER) != 0)
        handoff_fail("topology-sdt-window");

    uint32_t copied = 0;
    while (copied < length) {
        const uint64_t current = physical_address + copied;
        const uint64_t frame = current & ~(uint64_t)(PAGE_BYTES - 1u);
        const uint32_t offset = (uint32_t)(current & (PAGE_BYTES - 1u));
        uint32_t chunk = PAGE_BYTES - offset;
        if (chunk > length - copied) chunk = length - copied;
        ((volatile uint64_t *)page_table_a)[window_page] =
            frame | PTE_PRESENT | PTE_WRITABLE | PTE_NX;
        __asm__ volatile ("invlpg (%0)" : : "r"(window) : "memory");
        const volatile uint8_t *source =
            (const volatile uint8_t *)(window + offset);
        for (uint32_t byte = 0; byte < chunk; ++byte)
            destination[copied + byte] = source[byte];
        copied += chunk;
    }
    ((volatile uint64_t *)page_table_a)[window_page] = saved_leaf;
    __asm__ volatile ("invlpg (%0)" : : "r"(window) : "memory");
}

/* Copy one complete ACPI SDT into kernel-owned storage before generated
   validation sees it.  Address translation and this byte copy remain trusted;
   signature, declared-length, checksum, root-entry, and MADT admission checks
   remain the generated boundary's responsibility.  The caller supplies a
   dedicated immutable-after-copy arena so the selected root and candidate
   table cannot alias each other. */
static __attribute__((unused)) struct copied_acpi_sdt copy_acpi_sdt(
        uint64_t physical_address, uint8_t *destination,
        uint32_t destination_capacity, uint32_t current_copy_offset) {
    if (physical_address > UINT64_C(0xffffffff))
        handoff_fail("topology-sdt-address-width");
    uint8_t header[36];
    copy_acpi_physical_bytes(physical_address, header, sizeof(header));
    uint32_t length = (uint32_t)header[4] |
        (uint32_t)header[5] << 8 |
        (uint32_t)header[6] << 16 |
        (uint32_t)header[7] << 24;
    if (length < 36u || length > MAX_COPIED_ACPI_SDT_BYTES ||
        length > destination_capacity)
        handoff_fail("topology-sdt-length");
    copy_acpi_physical_bytes(physical_address, destination, length);
    uint64_t byte_offset = 0;
    uint64_t next_copy_offset = current_copy_offset;
    while (byte_offset < length) {
        const uint32_t remaining = length - (uint32_t)byte_offset;
        const uint32_t chunk_bytes = remaining < 8u ? remaining : 8u;
        uint64_t physical_chunk = 0;
        for (uint32_t byte = 0; byte < chunk_bytes; ++byte)
            physical_chunk |=
                (uint64_t)destination[byte_offset + byte] << (byte * 8u);
        const uint64_t terminal = byte_offset + chunk_bytes == length;
#define COPY_STREAM_QUERY(query) leanos_boot_machine_acpi_copy_stream_step_query( \
            next_copy_offset, physical_address, byte_offset, physical_address, \
            length, byte_offset, physical_chunk, terminal, (query))
        const uint64_t status = COPY_STREAM_QUERY(1);
        const uint64_t error = COPY_STREAM_QUERY(2);
        const uint64_t next_byte = COPY_STREAM_QUERY(4);
        const uint64_t emitted_copy_offset = COPY_STREAM_QUERY(5);
        const uint64_t exposed = COPY_STREAM_QUERY(6);
#undef COPY_STREAM_QUERY
        if (error == 43) handoff_fail("topology-table-copy-budget");
        if (error == 44) handoff_fail("topology-table-copy-length");
        if (error == 45) handoff_fail("topology-table-copy-address");
        if (error == 46) handoff_fail("topology-table-copy-offset");
        if (error == 47) handoff_fail("topology-table-copy-terminal");
        if (error != 0) handoff_fail("topology-table-copy-error");
        if (status != 1) handoff_fail("topology-table-copy-status");
        if (next_byte != byte_offset + chunk_bytes)
            handoff_fail("topology-table-copy-next-byte");
        if (exposed != physical_chunk)
            handoff_fail("topology-table-copy-exposed");
        if (!terminal && emitted_copy_offset != next_copy_offset)
            handoff_fail("topology-table-copy-partial-cursor");
        if (terminal && emitted_copy_offset <= next_copy_offset)
            handoff_fail("topology-table-copy-final-cursor");
        for (uint32_t byte = 0; byte < chunk_bytes; ++byte)
            destination[byte_offset + byte] =
                (uint8_t)(exposed >> (byte * 8u));
        byte_offset = next_byte;
        if (terminal) next_copy_offset = emitted_copy_offset;
    }
    return (struct copied_acpi_sdt) {
        .physical_address = physical_address,
        .bytes = destination,
        .length = length,
        .next_copy_offset = (uint32_t)next_copy_offset
    };
}

static int acpi_signature_matches(
        const struct copied_acpi_sdt *table, const char signature[4]) {
    return table->length >= 36u &&
        table->bytes[0] == (uint8_t)signature[0] &&
        table->bytes[1] == (uint8_t)signature[1] &&
        table->bytes[2] == (uint8_t)signature[2] &&
        table->bytes[3] == (uint8_t)signature[3];
}

/* Admit only the immutable copy: copied header, declared extent, expected
   signature (when supplied), and whole-table ACPI checksum must agree before
   root-entry decoding or MADT selection. */
static void validate_copied_acpi_sdt(
        const struct copied_acpi_sdt *table, const char *signature) {
    if (table->bytes == 0 || table->length < 36u ||
        ((uint32_t)table->bytes[4] |
         (uint32_t)table->bytes[5] << 8 |
         (uint32_t)table->bytes[6] << 16 |
         (uint32_t)table->bytes[7] << 24) != table->length ||
        (signature != 0 && !acpi_signature_matches(table, signature)))
        handoff_fail("topology-sdt-envelope");
    uint8_t checksum = 0;
    for (uint32_t byte = 0; byte < table->length; ++byte)
        checksum = (uint8_t)(checksum + table->bytes[byte]);
    if (checksum != 0) handoff_fail("topology-sdt-checksum");
}

static const struct copied_acpi_sdt *select_unique_copied_madt(
        uint32_t copied_count) {
    const struct copied_acpi_sdt *selected = 0;
    for (uint32_t index = 0; index < copied_count; ++index) {
        const struct copied_acpi_sdt *candidate =
            &boot_acpi_table_copies[index];
        validate_copied_acpi_sdt(candidate, 0);
        if (acpi_signature_matches(candidate, "APIC")) {
            if (selected != 0) handoff_fail("topology-madt-duplicate");
            selected = candidate;
        }
    }
    if (selected == 0) handoff_fail("topology-madt-missing");
    return selected;
}

/* Replay the selected immutable MADT copy through the generated byte-level
   envelope transition.  C supplies bytes and carries exact returned state;
   it does not recognize the signature, declared extent, terminal position,
   or checksum that authorize the later generated entry/admission stream. */
static void validate_generated_madt_envelope(
        const struct copied_acpi_sdt *madt) {
    uint64_t next_byte = 0, declared_length = 0, checksum = 0;
    for (uint64_t byte = 0; byte < madt->length; ++byte) {
        const uint64_t terminal = byte + 1 == madt->length;
#define MADT_ENVELOPE_QUERY(word) \
        leanos_boot_machine_madt_envelope_byte_step_query( \
            next_byte, declared_length, checksum, madt->length, byte, \
            madt->bytes[byte], terminal, (word))
        const uint64_t abi = MADT_ENVELOPE_QUERY(0);
        const uint64_t status = MADT_ENVELOPE_QUERY(1);
        const uint64_t error = MADT_ENVELOPE_QUERY(2);
        const uint64_t emitted_next_byte = MADT_ENVELOPE_QUERY(3);
        const uint64_t emitted_declared_length = MADT_ENVELOPE_QUERY(4);
        const uint64_t emitted_checksum = MADT_ENVELOPE_QUERY(5);
        const uint64_t exposed_byte = MADT_ENVELOPE_QUERY(6);
#undef MADT_ENVELOPE_QUERY
        if (abi != 1 || status != (terminal ? 3u : 1u) || error != 0 ||
            emitted_next_byte != byte + 1u ||
            exposed_byte != madt->bytes[byte])
            handoff_fail("topology-madt-generated-envelope");
        next_byte = emitted_next_byte;
        declared_length = emitted_declared_length;
        checksum = emitted_checksum;
    }
    if (next_byte != madt->length || declared_length != madt->length ||
        checksum != 0)
        handoff_fail("topology-madt-generated-envelope");
}

/* Consume every byte after the fixed MADT header through one generated,
   allocation-free state machine.  C carries the exact returned record state,
   enabled count, admitted APIC ID, and full 256-bit duplicate set; it does not
   classify record kinds, collapse duplicates, or assert singleton admission. */
static uint32_t validate_generated_madt_entries(
        const struct copied_acpi_sdt *madt, uint32_t executing_apic_id) {
    if (madt->length <= 44u || executing_apic_id > 255u)
        handoff_fail("topology-madt-generated-entries");
    uint64_t offset = 44, record_offset = 0, record_kind = 0;
    uint64_t record_length = 0, apic_id = 0, flags = 0;
    uint64_t enabled_count = 0, admitted_apic_id = 256;
    uint64_t seen0 = 0, seen1 = 0, seen2 = 0, seen3 = 0;
    while (offset < madt->length) {
#define MADT_ENTRY_QUERY(word) \
        leanos_boot_machine_madt_entry_stream_byte_step_query( \
            offset, record_offset, record_kind, record_length, apic_id, flags, \
            enabled_count, admitted_apic_id, seen0, seen1, seen2, seen3, \
            madt->length, executing_apic_id, offset, madt->bytes[offset], \
            (word))
        const uint64_t terminal = offset + 1u == madt->length;
        const uint64_t abi = MADT_ENTRY_QUERY(0);
        const uint64_t status = MADT_ENTRY_QUERY(1);
        const uint64_t error = MADT_ENTRY_QUERY(2);
        const uint64_t next_offset = MADT_ENTRY_QUERY(3);
        const uint64_t next_record_offset = MADT_ENTRY_QUERY(4);
        const uint64_t next_record_kind = MADT_ENTRY_QUERY(5);
        const uint64_t next_record_length = MADT_ENTRY_QUERY(6);
        const uint64_t next_apic_id = MADT_ENTRY_QUERY(7);
        const uint64_t next_flags = MADT_ENTRY_QUERY(8);
        const uint64_t next_enabled_count = MADT_ENTRY_QUERY(9);
        const uint64_t next_admitted_apic_id = MADT_ENTRY_QUERY(10);
        const uint64_t next_seen0 = MADT_ENTRY_QUERY(11);
        const uint64_t next_seen1 = MADT_ENTRY_QUERY(12);
        const uint64_t next_seen2 = MADT_ENTRY_QUERY(13);
        const uint64_t next_seen3 = MADT_ENTRY_QUERY(14);
        const uint64_t exposed_byte = MADT_ENTRY_QUERY(15);
#undef MADT_ENTRY_QUERY
        if (abi != 1 || status != (terminal ? 3u : 1u) || error != 0 ||
            next_offset != offset + 1u || exposed_byte != madt->bytes[offset])
            handoff_fail("topology-madt-generated-entries");
        offset = next_offset;
        record_offset = next_record_offset;
        record_kind = next_record_kind;
        record_length = next_record_length;
        apic_id = next_apic_id;
        flags = next_flags;
        enabled_count = next_enabled_count;
        admitted_apic_id = next_admitted_apic_id;
        seen0 = next_seen0;
        seen1 = next_seen1;
        seen2 = next_seen2;
        seen3 = next_seen3;
    }
    if (offset != madt->length || record_offset != 0 || record_kind != 0 ||
        record_length != 0 || apic_id != 0 || flags != 0 ||
        enabled_count != 1 || admitted_apic_id > 255u ||
        admitted_apic_id != executing_apic_id ||
        (seen0 | seen1 | seen2 | seen3) == 0)
        handoff_fail("topology-madt-generated-entries");
    return (uint32_t)admitted_apic_id;
}

/* Final scalar bridge from the byte-consuming generated MADT admission state
   to production publication.  The caller must supply status/detail/APIC words
   emitted by that generated state; C-derived envelope/checksum checks cannot
   substitute for them.  Keeping this helper separate makes the remaining
   boot_allocate wiring fail closed instead of re-encoding the policy in C. */
static __attribute__((unused)) uint32_t require_machine_topology_admission(
        uint64_t selected_kind, uint64_t selected_address,
        uint64_t copied_root_address, uint64_t advertised_count,
        uint64_t completed_copies, uint64_t madt_count,
        uint64_t admission_status, uint64_t admission_detail,
        uint64_t admitted_apic_id, uint64_t executing_apic_id) {
#define TOPOLOGY_RESULT_QUERY(word) \
    leanos_boot_machine_topology_admission_result_query( \
        selected_kind, selected_address, copied_root_address, \
        advertised_count, completed_copies, madt_count, admission_status, \
        admission_detail, admitted_apic_id, executing_apic_id, (word))
    const uint64_t abi = TOPOLOGY_RESULT_QUERY(0);
    const uint64_t status = TOPOLOGY_RESULT_QUERY(1);
    const uint64_t error = TOPOLOGY_RESULT_QUERY(2);
    const uint64_t admitted = TOPOLOGY_RESULT_QUERY(3);
#undef TOPOLOGY_RESULT_QUERY
    if (abi != 1 || status != 1 || error != 0 || admitted > UINT32_MAX ||
        admitted != admitted_apic_id || admitted != executing_apic_id)
        handoff_fail("topology-admission-result");
    return (uint32_t)admitted;
}

/* Bind the copied root payload shape to the generated RSDT/XSDT selection
   before any advertised physical address is translated.  The 256-entry cap
   is the machine rendering of BootTopology.maxAcpiRootEntries. */
static struct acpi_root_entries decode_acpi_root_entries(
        const struct copied_acpi_sdt *root, uint64_t selected_kind) {
    uint32_t width;
    if (selected_kind == 1u) width = 4u;
    else if (selected_kind == 2u) width = 8u;
    else handoff_fail("topology-root-kind");
    if (root->length < 36u) handoff_fail("topology-root-header");
    const uint32_t payload = root->length - 36u;
    if (payload % width != 0u) handoff_fail("topology-root-width");
    const uint32_t count = payload / width;
    if (count > MAX_ACPI_ROOT_ENTRIES)
        handoff_fail("topology-root-entries");
    return (struct acpi_root_entries) {
        .bytes = root->bytes + 36u,
        .count = count,
        .width = width
    };
}

static uint64_t decode_acpi_root_entry(
        const struct acpi_root_entries *entries, uint32_t index) {
    if (index >= entries->count ||
        (entries->width != 4u && entries->width != 8u))
        handoff_fail("topology-root-entry-index");
    uint64_t physical_address = 0;
    const uint8_t *encoded = entries->bytes + index * entries->width;
    for (uint32_t byte = 0; byte < entries->width; ++byte)
        physical_address |= (uint64_t)encoded[byte] << (byte * 8u);
    if (physical_address == 0 || physical_address > UINT64_C(0xffffffff))
        handoff_fail("topology-root-entry-address");
    return physical_address;
}

/* Translate every advertised root entry into a disjoint kernel-owned byte
   range before firmware memory can be scrubbed or reused.  The one-MiB
   aggregate cap is a deliberately tighter machine boundary than the model's
   per-table 64-KiB cap: a root whose complete translation does not fit is
   rejected rather than partially admitted. */
static uint32_t copy_acpi_root_tables(
        const struct acpi_root_entries *entries,
        const uint64_t addresses[MAX_ACPI_ROOT_ENTRIES]) {
    if (entries->count == 0)
        handoff_fail("topology-table-copy-sequence");
    uint32_t arena_offset = 0;
    uint64_t copied_ordinal = 0;
    for (uint32_t entry = 0; entry < entries->count; ++entry) {
        if (arena_offset >= MAX_COPIED_ACPI_TABLE_BYTES)
            handoff_fail("topology-table-copy-budget");
        const struct copied_acpi_sdt copied = copy_acpi_sdt(
            addresses[entry], boot_acpi_table_copy + arena_offset,
            MAX_COPIED_ACPI_TABLE_BYTES - arena_offset, arena_offset);
        if (copied.physical_address != addresses[entry] ||
            copied.bytes != boot_acpi_table_copy + arena_offset)
            handoff_fail("topology-table-copy-binding");
        boot_acpi_table_copies[entry] = copied;
        const uint32_t padded_length = (copied.length + 7u) & ~7u;
        if (padded_length < copied.length ||
            padded_length > MAX_COPIED_ACPI_TABLE_BYTES - arena_offset)
            handoff_fail("topology-table-copy-budget");
        if (copied.next_copy_offset != arena_offset + padded_length)
            handoff_fail("topology-table-copy-stream");
        arena_offset += padded_length;
        const uint64_t final_table = entry + 1u == entries->count;
        const uint64_t status =
            leanos_boot_machine_acpi_copy_sequence_step_query(
                copied_ordinal, entries->count, entry, 1, final_table, 1);
        const uint64_t error =
            leanos_boot_machine_acpi_copy_sequence_step_query(
                copied_ordinal, entries->count, entry, 1, final_table, 2);
        const uint64_t next_ordinal =
            leanos_boot_machine_acpi_copy_sequence_step_query(
                copied_ordinal, entries->count, entry, 1, final_table, 3);
        if (status != 1 || error != 0 || next_ordinal != entry + 1u)
            handoff_fail("topology-table-copy-sequence");
        copied_ordinal = next_ordinal;
    }
    if (copied_ordinal != entries->count)
        handoff_fail("topology-table-copy-sequence");
    return entries->count;
}

/* CPUID.1:EBX[31:24] is the initial APIC ID of the processor executing this
   instruction.  This is a trusted hardware observation, not topology
   admission: the copied ACPI root/table pipeline must still prove that this
   ID names the sole enabled processor before runtime publication. */
static uint32_t observe_executing_apic_id(void) {
    uint32_t max_leaf, leaf_b, leaf_c, leaf_d;
    __asm__ volatile ("cpuid"
        : "=a"(max_leaf), "=b"(leaf_b), "=c"(leaf_c), "=d"(leaf_d)
        : "a"(0u), "c"(0u));
    if (max_leaf < 1u) handoff_fail("topology-cpuid-leaf");
    __asm__ volatile ("cpuid"
        : "=a"(max_leaf), "=b"(leaf_b), "=c"(leaf_c), "=d"(leaf_d)
        : "a"(1u), "c"(0u));
    if (((leaf_d >> 9) & 1u) == 0u)
        handoff_fail("topology-cpuid-apic");
    return leaf_b >> 24;
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
static struct copied_boot_handoff copy_boot_handoff(
        uint32_t magic, uint32_t info_address, uint32_t total,
        uint32_t executing_apic_id) {
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
    return (struct copied_boot_handoff) {
        .bytes = boot_handoff_copy,
        .length = total,
        .executing_apic_id = executing_apic_id
    };
}

struct boot_decode_state { uint64_t word[41]; };

static void zero_boot_decode_state(struct boot_decode_state *state) {
    volatile uint64_t *words = state->word;
    for (unsigned query = 0; query < 41; ++query)
        words[query] = 0;
}

/* Keep fixed-width decoder-state transport explicit in the freestanding
   kernel. Clang may otherwise lower these aggregate copies to a hosted
   memcpy call, which is not part of the boot image's runtime contract. */
static void copy_boot_decode_state(struct boot_decode_state *destination,
                                   const struct boot_decode_state *source) {
    volatile uint64_t *words = destination->word;
    for (unsigned query = 0; query < 41; ++query)
        words[query] = source->word[query];
}

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

#define BOOT_BITMAP_ARGS(words) \
    (words)[0], (words)[1], (words)[2], (words)[3], \
    (words)[4], (words)[5], (words)[6], (words)[7], \
    (words)[8], (words)[9], (words)[10], (words)[11], \
    (words)[12], (words)[13], (words)[14], (words)[15], \
    (words)[16], (words)[17], (words)[18], (words)[19], \
    (words)[20], (words)[21], (words)[22], (words)[23], \
    (words)[24], (words)[25], (words)[26], (words)[27], \
    (words)[28], (words)[29], (words)[30], (words)[31], \
    (words)[32], (words)[33], (words)[34], (words)[35], \
    (words)[36], (words)[37], (words)[38], (words)[39], \
    (words)[40], (words)[41], (words)[42], (words)[43], \
    (words)[44], (words)[45], (words)[46], (words)[47], \
    (words)[48], (words)[49], (words)[50], (words)[51], \
    (words)[52], (words)[53], (words)[54], (words)[55], \
    (words)[56], (words)[57], (words)[58], (words)[59], \
    (words)[60], (words)[61], (words)[62], (words)[63]

/* Parse the immutable copy exactly once.  The generated transition emits each
   canonical decoded entry on its accepting type step; C only retains those
   typed events and the generated 4096-frame bounded projection. */
static struct boot_decode_state decode_boot_projection(
        uint32_t magic, uint32_t info_address, uint32_t total,
        const uint8_t *info) {
    struct boot_decode_state state, next;
    for (uint64_t block = 0; block < 64; ++block) {
        boot_projection_usable[block] = 0;
        boot_projection_blocked[block] = 0;
        boot_projection_reserved[block] = 0;
    }
    for (uint64_t query = 0; query < 41; ++query)
        state.word[query] =
            leanos_boot_decode_init_v5(magic, info_address, total, 0, query);
    if (state.word[0] != 5 || state.word[1] != 0 || state.word[2] != 0 ||
        state.word[3] != info_address || state.word[4] != total ||
        state.word[5] != 0 || state.word[16] != 0 ||
        state.word[18] != 0 || state.word[30] != 0)
        handoff_fail("decode-init");
    for (uint64_t offset = 0; offset < total; offset += 8) {
        uint64_t chunk = *(const uint64_t *)(info + offset);
        uint64_t terminal = offset + 8 == total;
        for (uint64_t query = 0; query < 41; ++query)
            next.word[query] = leanos_boot_decode_step_v5(
                state.word[0], state.word[1], state.word[2], state.word[3],
                state.word[4], state.word[5], state.word[6], state.word[7],
                state.word[8], state.word[9], state.word[10], state.word[11],
                state.word[12], state.word[13], state.word[14], state.word[15],
                state.word[16], state.word[17], state.word[18], state.word[23],
                state.word[24], state.word[25], state.word[26], state.word[27],
                state.word[28], state.word[29], state.word[30], state.word[31],
                state.word[32], state.word[33], state.word[34], state.word[35],
                state.word[36], state.word[37], state.word[38],
                info_address, offset, chunk, terminal, query);
        copy_boot_decode_state(&state, &next);
        if (state.word[2] != 0) break;
        if (state.word[19] == 1) {
            if (state.word[11] == 0 || state.word[11] > 256)
                handoff_fail("projection-entry-count");
            uint64_t slot = state.word[11] - 1;
            boot_projection_entries[slot].base = state.word[20];
            boot_projection_entries[slot].length = state.word[21];
            boot_projection_entries[slot].kind = state.word[22];
            for (uint64_t block = 0; block < 64; ++block) {
                uint64_t status = leanos_boot_projection_entry(
                    state.word[20], state.word[21], state.word[22], block,
                    boot_projection_usable[block],
                    boot_projection_blocked[block], 1);
                uint64_t error = leanos_boot_projection_entry(
                    state.word[20], state.word[21], state.word[22], block,
                    boot_projection_usable[block],
                    boot_projection_blocked[block], 2);
                uint64_t usable = leanos_boot_projection_entry(
                    state.word[20], state.word[21], state.word[22], block,
                    boot_projection_usable[block],
                    boot_projection_blocked[block], 3);
                uint64_t blocked = leanos_boot_projection_entry(
                    state.word[20], state.word[21], state.word[22], block,
                    boot_projection_usable[block],
                    boot_projection_blocked[block], 4);
                if (status != 1 || error != 0)
                    handoff_fail("projection-entry");
                boot_projection_usable[block] = usable;
                boot_projection_blocked[block] = blocked;
            }
        }
    }
    if (state.word[2] == 0 &&
        (state.word[1] != 1 || state.word[5] != total || state.word[7] != 7))
        handoff_fail("decode-incomplete");
    return state;
}

/* Re-run the same generated decoder for the candidate selected from the
   bounded projection.  This scalar terminal state is the authorization gate:
   caller-owned projection storage may suggest a candidate, but cannot grant
   usable-frame or non-overlap authority. */
static struct boot_decode_state decode_boot_candidate_authority(
        uint32_t magic, uint32_t info_address, uint32_t total,
        uint64_t candidate, const uint8_t *info) {
    struct boot_decode_state state, next;
    for (uint64_t query = 0; query < 41; ++query)
        state.word[query] =
            leanos_boot_decode_init_v5(
                magic, info_address, total, candidate, query);
    if (state.word[0] != 5 || state.word[1] != 0 || state.word[2] != 0 ||
        state.word[3] != info_address || state.word[4] != total ||
        state.word[5] != 0 || state.word[16] != candidate ||
        state.word[18] != 0 || state.word[30] != 0)
        handoff_fail("authority-init");
    for (uint64_t offset = 0; offset < total; offset += 8) {
        uint64_t chunk = *(const uint64_t *)(info + offset);
        uint64_t terminal = offset + 8 == total;
        for (uint64_t query = 0; query < 41; ++query)
            next.word[query] = leanos_boot_decode_step_v5(
                state.word[0], state.word[1], state.word[2], state.word[3],
                state.word[4], state.word[5], state.word[6], state.word[7],
                state.word[8], state.word[9], state.word[10], state.word[11],
                state.word[12], state.word[13], state.word[14], state.word[15],
                state.word[16], state.word[17], state.word[18], state.word[23],
                state.word[24], state.word[25], state.word[26], state.word[27],
                state.word[28], state.word[29], state.word[30], state.word[31],
                state.word[32], state.word[33], state.word[34], state.word[35],
                state.word[36], state.word[37], state.word[38],
                info_address, offset, chunk, terminal, query);
        copy_boot_decode_state(&state, &next);
        if (state.word[2] != 0) break;
    }
    if (state.word[1] != 1 || state.word[2] != 0 ||
        state.word[5] != total || state.word[7] != 7 ||
        state.word[16] != candidate)
        handoff_fail("authority-rejected");
    return state;
}

struct boot_terminal_result { uint64_t word[9]; };

static uint64_t projection_finish_query(
        const struct boot_decode_state *decoded, uint64_t owner,
        uint64_t manifest_status, uint64_t manifest_error,
        uint64_t query, const uint64_t *free_words) {
    return leanos_boot_projection_finish(
        decoded->word[1], decoded->word[2], manifest_status, manifest_error,
        decoded->word[11], decoded->word[17], owner, query,
        BOOT_BITMAP_ARGS(free_words));
}

/* The generated raw-word decoder is the sole tag walker and classifier.  Its
   typed entry events build the complete bounded rich projection in one pass;
   generated manifest overlay and terminal selection return one typed result.
   C only transports fixed-width words and executes scrub/publication. */
static void boot_allocate(uint32_t magic, uint32_t info_address) {
    if (magic != MULTIBOOT2_RUNTIME_MAGIC) handoff_fail("magic");
    if ((info_address & 7u) != 0 || info_address < PAGE_BYTES ||
        info_address >= BOOT_ACCESSIBLE_LIMIT) handoff_fail("pointer");
    const uint8_t *physical = (const uint8_t *)(uint64_t)info_address;
    uint32_t total = *(const uint32_t *)physical;
    if (total < 16 || total > MAX_HANDOFF_BYTES || (total & 7u) != 0 ||
        total > BOOT_ACCESSIBLE_LIMIT - info_address) handoff_fail("bounds");
    const struct copied_boot_handoff handoff = copy_boot_handoff(
        magic, info_address, total, observe_executing_apic_id());
    const uint8_t *info = handoff.bytes;
    if (handoff.length != total)
        handoff_fail("topology-handoff-length");
    struct boot_decode_state decoded =
        decode_boot_projection(magic, info_address, total, info);
    if (decoded.word[1] != 1 || decoded.word[2] != 0)
        handoff_fail("decode-rejected");
    if ((decoded.word[39] != 1 && decoded.word[39] != 2) ||
        decoded.word[40] == 0)
        handoff_fail("topology-root-selection");
    const struct copied_acpi_sdt selected_root =
        copy_acpi_sdt(decoded.word[40], boot_acpi_root_copy,
            MAX_COPIED_ACPI_SDT_BYTES, 0);
    if (selected_root.physical_address != decoded.word[40] ||
        selected_root.bytes != boot_acpi_root_copy || selected_root.length < 36u)
        handoff_fail("topology-root-copy");
    validate_copied_acpi_sdt(
        &selected_root, decoded.word[39] == 1 ? "RSDT" : "XSDT");
    const struct acpi_root_entries root_entries =
        decode_acpi_root_entries(&selected_root, decoded.word[39]);
    if (root_entries.bytes != selected_root.bytes + 36u ||
        (root_entries.width != 4u && root_entries.width != 8u))
        handoff_fail("topology-root-vector");
    uint64_t root_table_addresses[MAX_ACPI_ROOT_ENTRIES];
    for (uint32_t entry = 0; entry < root_entries.count; ++entry) {
        root_table_addresses[entry] =
            decode_acpi_root_entry(&root_entries, entry);
        for (uint32_t prior = 0; prior < entry; ++prior)
            if (root_table_addresses[prior] == root_table_addresses[entry])
                handoff_fail("topology-root-entry-duplicate");
    }
    const uint32_t copied_table_count =
        copy_acpi_root_tables(&root_entries, root_table_addresses);
    if (copied_table_count != root_entries.count)
        handoff_fail("topology-table-copy-incomplete");
    const struct copied_acpi_sdt *selected_madt =
        select_unique_copied_madt(copied_table_count);
    if (!acpi_signature_matches(selected_madt, "APIC"))
        handoff_fail("topology-madt-selection");
    validate_generated_madt_envelope(selected_madt);
    const uint32_t admitted_apic_id = validate_generated_madt_entries(
        selected_madt, handoff.executing_apic_id);
    const uint32_t published_apic_id = require_machine_topology_admission(
        decoded.word[39], decoded.word[40], selected_root.physical_address,
        root_entries.count, copied_table_count, 1, 1, 0,
        admitted_apic_id, handoff.executing_apic_id);
    if (published_apic_id != handoff.executing_apic_id)
        handoff_fail("topology-admission-publication");
    uint64_t free_words[64];
    uint64_t manifest_status = 1, manifest_error = 0;
    for (uint64_t block = 0; block < 64; ++block) {
        uint64_t status = leanos_boot_projection_manifest(
            block, BOOT_MANIFEST_ARGS(info_address, total), 1);
        uint64_t error = leanos_boot_projection_manifest(
            block, BOOT_MANIFEST_ARGS(info_address, total), 2);
        uint64_t reserved = leanos_boot_projection_manifest(
            block, BOOT_MANIFEST_ARGS(info_address, total), 3);
        if (status != 1 || error != 0) {
            manifest_status = status;
            manifest_error = error;
        }
        boot_projection_reserved[block] = reserved;
        free_words[block] = leanos_boot_projection_free(
            boot_projection_usable[block], boot_projection_blocked[block],
            boot_projection_reserved[block]);
    }
    struct boot_terminal_result authority;
    for (uint64_t query = 0; query < 9; ++query)
        authority.word[query] =
            projection_finish_query(
                &decoded, 1, manifest_status, manifest_error, query, free_words);
    if (authority.word[0] != 1 || authority.word[1] != 1 ||
        authority.word[2] != 0 || authority.word[3] >= 4096 ||
        authority.word[4] != 1 || authority.word[5] != decoded.word[11])
        handoff_fail("projection-terminal");
    /* Select from target-specific replays of the immutable raw handoff.  The
       projection bitmap remains a complete cross-check, but it no longer gets
       to nominate the frame consumed by production. */
    uint64_t selected = 4096;
    uint64_t selected_manifest = 0;
    struct boot_decode_state selected_authority;
    zero_boot_decode_state(&selected_authority);
#ifdef LEANOS_FRAME_BUDGET_SCENARIO
    uint64_t next_selected = 4096;
#endif
    for (uint64_t candidate = 0; candidate < 4096; ++candidate) {
        struct boot_decode_state candidate_authority =
            decode_boot_candidate_authority(
                magic, info_address, total, candidate, info);
        uint64_t candidate_manifest = leanos_boot_manifest_candidate(
            candidate, BOOT_MANIFEST_ARGS(info_address, total));
        uint64_t exact_candidate = leanos_boot_consume_exact_projection(
            4096, candidate, candidate_authority.word[1],
            candidate_authority.word[14], candidate_authority.word[15],
            candidate_manifest);
        if (exact_candidate >= 4096) continue;
        if (selected >= 4096) {
            selected = exact_candidate;
            copy_boot_decode_state(&selected_authority, &candidate_authority);
            selected_manifest = candidate_manifest;
#ifndef LEANOS_FRAME_BUDGET_SCENARIO
            break;
#endif
#ifdef LEANOS_FRAME_BUDGET_SCENARIO
        } else {
            next_selected = exact_candidate;
            break;
#endif
        }
    }
    /* Production mutation fixture: corrupt only the complete-projection
       nomination after the immutable-byte replay has selected its frame.
       The comparison below must reject before either scrub or publication. */
#ifdef LEANOS_PROJECTION_SELECTION_MUTATION_FIXTURE
    const uint64_t exact_replay_selected = selected;
    authority.word[3] = selected == 4095 ? selected - 1 : selected + 1;
    /* Preserve the rest of the boot image as reachable evidence while making
       the fixture value opaque to compile-time control-flow elimination. */
    __asm__ volatile ("" : "+m"(authority.word[3]));
    if (selected != exact_replay_selected)
        handoff_fail("projection-mutation-raw-selection");
#endif
    /* Production mutation fixtures exercise the raw replay authority itself,
       rather than only the independent complete-projection cross-check. */
#ifdef LEANOS_RAW_SELECTION_MUTATION_FIXTURE
    selected = selected == 4095 ? selected - 1 : selected + 1;
#endif
#ifdef LEANOS_RAW_CLASSIFICATION_MUTATION_FIXTURE
    selected_authority.word[14] = 0;
#endif
    if (selected >= 4096 || authority.word[3] != selected ||
        selected_authority.word[16] != selected ||
        selected_authority.word[11] != decoded.word[11] ||
        selected_authority.word[17] != decoded.word[17] ||
        selected_authority.word[14] != 1 ||
        selected_authority.word[15] != 0 || selected_manifest != 1) {
#ifdef LEANOS_RAW_SELECTION_MUTATION_FIXTURE
        handoff_fail("raw-selection-authority");
#else
        handoff_fail("projection-authority");
#endif
    }

    volatile uint8_t *frame = (volatile uint8_t *)(selected * PAGE_BYTES);
    for (uint64_t i = 0; i < PAGE_BYTES; ++i) frame[i] = 0;
    for (uint64_t i = 0; i < PAGE_BYTES; ++i)
        if (frame[i] != 0) handoff_fail("scrub");
    struct boot_terminal_result publication = {0};
    for (uint64_t query = 0; query < 5; ++query)
        publication.word[query] = leanos_boot_authority_result(
            selected, selected_authority.word[16], selected_authority.word[1],
            selected_authority.word[14], selected_authority.word[15],
            selected_manifest, 1, query);
#ifdef LEANOS_PUBLICATION_RESULT_MUTATION_FIXTURE
    publication.word[3] = selected == 4095 ? selected - 1 : selected + 1;
#endif
    if (publication.word[0] != 1 || publication.word[1] != 1 ||
        publication.word[2] != 0 || publication.word[3] != selected ||
        publication.word[4] != selected + 1)
        handoff_fail("publication");
    published_boot_object = publication.word[4];
#ifdef LEANOS_FRAME_BUDGET_SCENARIO
    frame_budget_boot_published_frame = selected;
    frame_budget_physical_frame = next_selected;
    if (frame_budget_physical_frame >= 4096 ||
        frame_budget_physical_frame <= frame_budget_boot_published_frame)
        handoff_fail("frame-budget-unpublished-frame");
    struct boot_decode_state frame_budget_authority =
        decode_boot_candidate_authority(
            magic, info_address, total, frame_budget_physical_frame, info);
    frame_budget_rescanned_frame = frame_budget_authority.word[16];
    frame_budget_rescan_status = frame_budget_authority.word[1];
    frame_budget_rescan_usable = frame_budget_authority.word[14];
    frame_budget_rescan_blocked = frame_budget_authority.word[15];
    frame_budget_rescan_manifest = leanos_boot_manifest_candidate(
        frame_budget_physical_frame, BOOT_MANIFEST_ARGS(info_address, total));
    if (frame_budget_authority.word[11] != decoded.word[11] ||
        frame_budget_authority.word[17] != decoded.word[17] ||
        frame_budget_rescanned_frame != frame_budget_physical_frame ||
        frame_budget_rescan_status != 1 ||
        frame_budget_rescan_usable != 1 ||
        frame_budget_rescan_blocked != 0 ||
        frame_budget_rescan_manifest != 1)
        handoff_fail("frame-budget-projection-authority");
#endif

    serial_puts("LEANOS/7 HANDOFF magic=valid info-bytes="); serial_u64(total);
    serial_puts(" mmap-entries="); serial_u64(authority.word[5]);
    serial_puts(" result=PASS\n");
    serial_puts("LEANOS/7 MAP boot-pages=4096");
    serial_puts(" reported-top-mib=");
    serial_u64(authority.word[6] / (1024u * 1024u));
    serial_puts(" precedence=reserved result=PASS\n");
    serial_puts("LEANOS/7 ALLOC frame="); serial_u64(selected);
    serial_puts(" firmware-usable=1 boot-accessible=1 reserved=0 projection=scalar-checked result=PASS\n");
    serial_puts("LEANOS/7 SCRUB bytes=4096 zero=1 result=PASS\n");
    serial_puts("LEANOS/7 PUBLISH object=1 owner=1 stale-object=denied result=PASS\n");
    serial_puts("LEANOS/7 BOOTALLOC status=PASS\n");
#ifdef LEANOS_FRAME_BUDGET_SCENARIO
    serial_puts("LEANOS/20 FRAME physical-frame=");
    serial_u64(frame_budget_physical_frame);
    serial_puts(" boot-published-frame=");
    serial_u64(frame_budget_boot_published_frame);
    serial_puts(" prior-publications=0 distinct=1 source=scalar-stream-projection result=PASS\n");
#endif
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
    uint8_t required, assigned, bridge, multifunction;
};

#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
#define Q35_TOPOLOGY_TEXT "0001000800020003"
#define Q35_EXPECTED_PRESENT 6u
#else
#define Q35_TOPOLOGY_TEXT "0001000800020002"
#define Q35_EXPECTED_PRESENT 5u
#endif

/* This is the C rendering of DMAQuarantine.q35Manifest for topology version
   0x0001_0008_0002_0002. Configuration mechanism #1 and the behavior of these
   devices remain trusted hardware/QEMU inputs; acceptance is integration
   evidence and is not a refinement theorem for the Lean snapshot. */
static const struct pci_manifest_entry q35_pci_manifest[] = {
    { 0, 0, 0x8086, 0x29c0, 0x060000, 1, 0, 0, 0 },
    { 1, 0, 0x1234, 0x1111, 0x030000, 1, 0, 0, 0 },
    { 3, 0, 0x1af4, 0x1000, 0x020000, 0, 0, 0, 0 },
    { 31, 0, 0x8086, 0x2918, 0x060100, 1, 0, 1, 1 },
    { 31, 2, 0x8086, 0x2922, 0x010601, 1, 0, 0, 1 },
    { 31, 3, 0x8086, 0x2930, 0x0c0500, 1, 0, 0, 1 },
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
    /* The assigned image admits exactly the pinned QEMU EDU function.  It is
       still quarantined to Command=0 here; publishing its generated tables
       and enabling its reviewed memory/bus-master bits are later stages. */
    { 2, 0, 0x1234, 0x11e8, 0x00ff00, 1, 1, 0, 0 },
#endif
};

struct pci_snapshot_entry {
    uint16_t vendor, product;
    uint32_t class_code;
    uint16_t command_before, command_after;
    uint8_t present, assigned, bridge, multifunction;
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
        (uint64_t)entry->assigned << 1 |
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
            q35_live_pci_snapshot.functions[index].assigned = entry->assigned;
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
    if (present != Q35_EXPECTED_PRESENT || optional_absent != 1 ||
        writes != present || readbacks != present)
        fail("dma-q35-nic-none");

    /* Feed the canonical live identity/status/Command/assignment/bridge
       projection itself through the generated q35Snapshot boundary.  The
       assigned image keeps the first six production entries byte-identical.
       Its seventh EDU entry is independently bound by the exact generated
       assigned-authority projection before assigned tables can be installed. */
    q35_live_pci_snapshot.generated_result =
        leanos_validate_q35_dma_snapshot(
            1, UINT64_C(0x0001000800020002),
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
        serial_puts("LEANOS/15 DMA-FUNCTION manifest=1 topology="
            Q35_TOPOLOGY_TEXT " bdf=0:");
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
        serial_puts(" assigned=");
        serial_u64(entry->assigned);
        serial_puts(" bridge=");
        serial_u64(entry->bridge);
        serial_puts(" multifunction=");
        serial_u64(entry->multifunction);
        serial_puts(" policy=accepted\n");
    }
    serial_puts("LEANOS/15 DMA snapshot=1 topology=" Q35_TOPOLOGY_TEXT
        " bus=0 scanned=256 present=");
    serial_u64(present);
    serial_puts(" optional-absent=1 writes=");
    serial_u64(writes);
    serial_puts(" readbacks=");
    serial_u64(readbacks);
    serial_puts(" initial-bus-masters=");
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
                (command & ~PCI_COMMAND_MODEL_MASK) != 0)
                fail("dma-live-command");
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
            if ((entry->assigned && command !=
                    (PCI_COMMAND_MEMORY | PCI_COMMAND_BUS_MASTER)) ||
                (!entry->assigned && command != 0))
                fail("dma-live-assignment-command");
#else
            if ((command & PCI_COMMAND_BUS_MASTER) != 0)
                fail("dma-live-bus-master");
#endif
            seen |= 1u << index;
            ++present;
        }
    }
    for (unsigned i = 0;
         i < sizeof(q35_pci_manifest) / sizeof(q35_pci_manifest[0]); ++i) {
        if (!(seen & (1u << i)) && q35_pci_manifest[i].required)
            fail("dma-live-required-missing");
    }
    if (present != Q35_EXPECTED_PRESENT) fail("dma-live-inventory");
}

/* Reviewed VT-d MMIO accessors: the only code deriving pointers from the
   remapping unit's window. The register layout and QEMU's VT-d implementation
   remain trusted integration boundaries, not refinement claims. */
static __attribute__((noinline, noipa)) uint32_t vtd_mmio_read32(uint64_t offset) {
    return *(volatile uint32_t *)(__vtd_mmio_window_start + offset);
}

static __attribute__((noinline, noipa)) uint64_t vtd_mmio_read64(uint64_t offset) {
    return *(volatile uint64_t *)(__vtd_mmio_window_start + offset);
}

static __attribute__((noinline, noipa)) void vtd_mmio_write32(uint64_t offset,
        uint32_t value) {
    *(volatile uint32_t *)(__vtd_mmio_window_start + offset) = value;
}

static __attribute__((noinline, noipa)) void vtd_mmio_write64(uint64_t offset,
        uint64_t value) {
    *(volatile uint64_t *)(__vtd_mmio_window_start + offset) = value;
}

#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
/* Reviewed assigned-image EDU accessor.  The virtual window is generated as
   supervisor-only and is bound to the exact BAR read back from PCI config. */
static __attribute__((noinline, noipa)) uint32_t edu_mmio_read32(uint64_t offset) {
    return *(volatile uint32_t *)(__edu_mmio_window_start + offset);
}

static __attribute__((noinline, noipa)) uint64_t edu_mmio_read64(uint64_t offset) {
    return *(volatile uint64_t *)(__edu_mmio_window_start + offset);
}

static __attribute__((noinline, noipa)) void edu_mmio_write64(uint64_t offset,
        uint64_t value) {
    *(volatile uint64_t *)(__edu_mmio_window_start + offset) = value;
}

#ifdef LEANOS_ASSIGNED_EDU_WRONG_BAR_FIXTURE
#define EDU_BAR_BASE UINT32_C(0xFEB00000)
#else
#define EDU_BAR_BASE UINT32_C(0xFEA00000)
#endif
#define EDU_BAR_MASK UINT32_C(0xFFFFFFF0)
#define EDU_REG_ID 0x00
#define EDU_REG_DMA_SOURCE 0x80
#define EDU_REG_DMA_DESTINATION 0x88
#define EDU_REG_DMA_COUNT 0x90
#define EDU_REG_DMA_COMMAND 0x98
#define EDU_DMA_START UINT64_C(1)
#define EDU_DMA_FROM_DEVICE UINT64_C(2)
#define EDU_DEVICE_BUFFER UINT64_C(0x40000)
#define EDU_TRANSFER_BYTES UINT64_C(16)
#define EDU_DMA_POLL_BOUND 1000000u
#ifdef LEANOS_ASSIGNED_EDU_WRONG_MMIO_IDENTITY_FIXTURE
#define EDU_EXPECTED_ID UINT32_C(0x010000EC)
#else
#define EDU_EXPECTED_ID UINT32_C(0x010000ED)
#endif
#endif

#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
static volatile uint64_t assigned_edu_kernel_record[2];

static void edu_wait_transfer(void) {
    for (unsigned attempt = 0; attempt < EDU_DMA_POLL_BOUND; ++attempt)
        if (!(edu_mmio_read64(EDU_REG_DMA_COMMAND) & EDU_DMA_START)) return;
    fail("vtd-assigned-transfer-timeout");
}

static void vtd_invalidate_global_iotlb(void);

/* Execute the first fixed useful transfer pair only after the generated
   authority boundary accepts both requests.  The finite model uses 16-byte
   IOVAs; the generated hardware projection scales those two pages to 4 KiB
   while keeping the request identity, generation, length, and direction
   kernel-owned. */
static __attribute__((noinline)) void run_assigned_edu_transfers(void) {
    const uint64_t payload0 = UINT64_C(0x363121534f6e6165);
    const uint64_t payload1 = UINT64_C(0x4d4d554f492d5544);
    const uint64_t guard0 = UINT64_C(0xc35ac35ac35ac35a);
    const uint64_t guard1 = UINT64_C(0xa53ca53ca53ca53c);
    const uint64_t sentinel0 = UINT64_C(0x73656e74696e656c);
    const uint64_t sentinel1 = UINT64_C(0x2d726561642d6564);
    const uint64_t secret0 = UINT64_C(0x7365637265742d30);
    const uint64_t secret1 = UINT64_C(0x7365637265742d31);
    const uint64_t subject0 = UINT64_C(0x7375626a65637430);
    const uint64_t subject1 = UINT64_C(0x7375626a65637431);
    const uint64_t kernel0 = UINT64_C(0x6b65726e656c2d30);
    const uint64_t kernel1 = UINT64_C(0x6b65726e656c2d31);
    const uint64_t user_stack_page = (uint64_t)user_a_stack / PAGE_BYTES;

    if (leanos_validate_assigned_edu_transfer(
            1, LEANOS_VTD_ASSIGNED_SOURCE, LEANOS_VTD_ASSIGNED_GENERATION,
            LEANOS_VTD_MODEL_READ_IOVA, LEANOS_VTD_MODEL_READ_LENGTH, 1) != 0)
        fail("vtd-assigned-read-authority");
    if (leanos_validate_assigned_edu_transfer(
            1, LEANOS_VTD_ASSIGNED_SOURCE, LEANOS_VTD_ASSIGNED_GENERATION,
            LEANOS_VTD_MODEL_WRITE_IOVA, LEANOS_VTD_MODEL_WRITE_LENGTH, 2) != 0)
        fail("vtd-assigned-write-authority");

    volatile uint64_t *read_buffer =
        (volatile uint64_t *)vtd_assigned_read_buffer;
    volatile uint64_t *write_buffer =
        (volatile uint64_t *)vtd_assigned_write_buffer;
    volatile uint64_t *guard_before =
        (volatile uint64_t *)vtd_assigned_guard_before;
    volatile uint64_t *guard_after =
        (volatile uint64_t *)vtd_assigned_guard_after;
    for (uint64_t word = 0; word < PAGE_BYTES / sizeof(uint64_t); ++word) {
        guard_before[word] = guard0 ^ word;
        guard_after[word] = guard1 ^ word;
    }
    ((volatile uint64_t *)user_a_stack)[0] = subject0;
    ((volatile uint64_t *)user_a_stack)[1] = subject1;
    assigned_edu_kernel_record[0] = kernel0;
    assigned_edu_kernel_record[1] = kernel1;
    /* Snapshot after the initialization write has legitimately populated the
       CPU accessed/dirty metadata; later DMA must not change these entries. */
    const uint64_t protected_page_table_record[4] = {
        page_map_level_4_a[0], page_directory_pointer_a[0],
        page_directory_a[0], page_table_a[user_stack_page]
    };
    read_buffer[0] = payload0;
    read_buffer[1] = payload1;
    write_buffer[0] = 0;
    write_buffer[1] = 0;

    edu_mmio_write64(EDU_REG_DMA_SOURCE, 0);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, EDU_DEVICE_BUFFER);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COMMAND, EDU_DMA_START);
    edu_wait_transfer();
    if (read_buffer[0] != payload0 || read_buffer[1] != payload1)
        fail("vtd-assigned-read-source");

    edu_mmio_write64(EDU_REG_DMA_SOURCE, EDU_DEVICE_BUFFER);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, PAGE_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(
        EDU_REG_DMA_COMMAND, EDU_DMA_START | EDU_DMA_FROM_DEVICE);
    edu_wait_transfer();
    if (write_buffer[0] != payload0 || write_buffer[1] != payload1)
        fail("vtd-assigned-write-result");
    if (guard_before[0] != guard0 || guard_after[0] != guard1)
        fail("vtd-assigned-transfer-canary");
    if (vtd_mmio_read32(0x34) != 0)
        fail("vtd-assigned-transfer-fault");

    /* Preload an independent device sentinel through the authorized read
       window, then attempt the same direction against the write-only IOVA.
       Bind the typed hardware fault to the current assignment before using
       authorized writes to prove the target did not receive the secret and
       an adjacent device-local sentinel record remained unchanged. */
    read_buffer[0] = sentinel0;
    read_buffer[1] = sentinel1;
    write_buffer[0] = secret0;
    write_buffer[1] = secret1;
    edu_mmio_write64(EDU_REG_DMA_SOURCE, 0);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, EDU_DEVICE_BUFFER);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COMMAND, EDU_DMA_START);
    edu_wait_transfer();
    /* QEMU's EDU DMA helper zero-fills the failed read destination. Preserve
       this second copy outside that target as the independent sentinel. */
    edu_mmio_write64(EDU_REG_DMA_SOURCE, 0);
    edu_mmio_write64(
        EDU_REG_DMA_DESTINATION, EDU_DEVICE_BUFFER + EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COMMAND, EDU_DMA_START);
    edu_wait_transfer();
    /* The preceding authorized write populated QEMU's IOTLB for this IOVA.
       Force a fresh second-level permission walk so the wrong-direction read
       must produce the typed VT-d fault required by the evidence contract. */
    vtd_invalidate_global_iotlb();
    edu_mmio_write64(EDU_REG_DMA_SOURCE, PAGE_BYTES);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, EDU_DEVICE_BUFFER);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COMMAND, EDU_DMA_START);
    edu_wait_transfer();
    uint64_t fault_status = vtd_mmio_read32(0x34);
    uint64_t fault_low = vtd_mmio_read64(0x220);
    uint64_t fault_high = vtd_mmio_read64(0x228);
    uint64_t fault_binding = leanos_validate_assigned_edu_fault(
            1, LEANOS_VTD_ASSIGNED_SOURCE, LEANOS_VTD_ASSIGNED_DOMAIN,
#ifdef LEANOS_ASSIGNED_EDU_FORGED_FAULT_FIXTURE
            LEANOS_VTD_ASSIGNED_GENERATION, 0, 1,
#else
            LEANOS_VTD_ASSIGNED_GENERATION, PAGE_BYTES, 1,
#endif
            fault_status, fault_low, fault_high);
    if (fault_binding != 0) {
        serial_puts("LEANOS/21 VTD-FAULT binding=");
        serial_u64(fault_binding);
        serial_puts(" fsts="); serial_u64(fault_status);
        serial_puts(" low="); serial_u64(fault_low);
        serial_puts(" high="); serial_u64(fault_high);
        edu_mmio_write64(EDU_REG_DMA_SOURCE, EDU_DEVICE_BUFFER);
        edu_mmio_write64(EDU_REG_DMA_DESTINATION, PAGE_BYTES);
        edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
        edu_mmio_write64(
            EDU_REG_DMA_COMMAND, EDU_DMA_START | EDU_DMA_FROM_DEVICE);
        edu_wait_transfer();
        serial_puts(" device-buffer=");
        serial_puts(write_buffer[0] == sentinel0 && write_buffer[1] == sentinel1
            ? "sentinel"
            : write_buffer[0] == secret0 && write_buffer[1] == secret1
                ? "secret" : "other");
        serial_puts(" observed0="); serial_u64(write_buffer[0]);
        serial_puts(" observed1="); serial_u64(write_buffer[1]);
        serial_puts(" result=REJECTED\n");
        fail("vtd-assigned-fault-binding");
    }
#ifdef LEANOS_ASSIGNED_EDU_WRONG_FAULT_VICTIM_FIXTURE
    write_buffer[0] ^= UINT64_C(1);
#endif
    if (write_buffer[0] != secret0 || write_buffer[1] != secret1 ||
        guard_before[0] != guard0 || guard_after[0] != guard1)
        fail("vtd-assigned-fault-victim");
    vtd_mmio_write64(0x228, UINT64_C(1) << 63);
    if (vtd_mmio_read32(0x34) != 0)
        fail("vtd-assigned-fault-clear");
    edu_mmio_write64(EDU_REG_DMA_SOURCE, EDU_DEVICE_BUFFER);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, PAGE_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(
        EDU_REG_DMA_COMMAND, EDU_DMA_START | EDU_DMA_FROM_DEVICE);
    edu_wait_transfer();
    if (write_buffer[0] == secret0 && write_buffer[1] == secret1)
        fail("vtd-assigned-read-secret");
    write_buffer[0] = 0;
    write_buffer[1] = 0;
    edu_mmio_write64(
        EDU_REG_DMA_SOURCE, EDU_DEVICE_BUFFER + EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, PAGE_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(
        EDU_REG_DMA_COMMAND, EDU_DMA_START | EDU_DMA_FROM_DEVICE);
    edu_wait_transfer();
    if (write_buffer[0] != sentinel0 || write_buffer[1] != sentinel1)
        fail("vtd-assigned-sentinel-record");
    serial_puts("LEANOS/21 VTD-FAULT requester=16 domain=0 generation=1"
        " direction=read iova=4096 reason=6 sid=16 sentinel=unchanged"
        " victim=unchanged state=current result=PASS\n");

    /* Attempt the converse wrong-direction transfer: the preserved device
       sentinel may not be written into the read-only IOVA. Bind the second
       hardware record before accepting the unchanged complete CPU record. */
    read_buffer[0] = secret0;
    read_buffer[1] = secret1;
    vtd_invalidate_global_iotlb();
    edu_mmio_write64(
        EDU_REG_DMA_SOURCE, EDU_DEVICE_BUFFER + EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, 0);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(
        EDU_REG_DMA_COMMAND, EDU_DMA_START | EDU_DMA_FROM_DEVICE);
    edu_wait_transfer();
    fault_status = vtd_mmio_read32(0x34);
    fault_low = vtd_mmio_read64(0x220);
    fault_high = vtd_mmio_read64(0x228);
    fault_binding = leanos_validate_assigned_edu_fault(
            1, LEANOS_VTD_ASSIGNED_SOURCE, LEANOS_VTD_ASSIGNED_DOMAIN,
            LEANOS_VTD_ASSIGNED_GENERATION, 0, 2,
            fault_status, fault_low, fault_high);
    if (fault_binding != 0) {
        serial_puts("LEANOS/21 VTD-WRITE-FAULT binding=");
        serial_u64(fault_binding);
        serial_puts(" fsts="); serial_u64(fault_status);
        serial_puts(" low="); serial_u64(fault_low);
        serial_puts(" high="); serial_u64(fault_high);
        serial_puts(" result=REJECTED\n");
        fail("vtd-assigned-write-fault-binding");
    }
    if (read_buffer[0] != secret0 || read_buffer[1] != secret1 ||
        write_buffer[0] != sentinel0 || write_buffer[1] != sentinel1 ||
        guard_before[0] != guard0 || guard_after[0] != guard1)
        fail("vtd-assigned-write-fault-victim");
    vtd_mmio_write64(0x228, UINT64_C(1) << 63);
    if (vtd_mmio_read32(0x34) != 0)
        fail("vtd-assigned-write-fault-clear");
    write_buffer[0] = 0;
    write_buffer[1] = 0;
    edu_mmio_write64(
        EDU_REG_DMA_SOURCE, EDU_DEVICE_BUFFER + EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, PAGE_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(
        EDU_REG_DMA_COMMAND, EDU_DMA_START | EDU_DMA_FROM_DEVICE);
    edu_wait_transfer();
    if (write_buffer[0] != sentinel0 || write_buffer[1] != sentinel1)
        fail("vtd-assigned-write-fault-sentinel");
    serial_puts("LEANOS/21 VTD-FAULT requester=16 domain=0 generation=1"
        " direction=write iova=0 reason=5 sid=16 sentinel=unchanged"
        " victim=unchanged state=current result=PASS\n");

    /* QEMU checks second-level read permission before reserved/presence
       validity, so a zero leaf reports the typed read fault. Bind its wholly
       unmapped IOVA while all four complete protected records stay intact. */
    read_buffer[0] = payload0;
    read_buffer[1] = payload1;
    write_buffer[0] = secret0;
    write_buffer[1] = secret1;
    vtd_invalidate_global_iotlb();
    edu_mmio_write64(EDU_REG_DMA_SOURCE, 2 * PAGE_BYTES);
    edu_mmio_write64(EDU_REG_DMA_DESTINATION, EDU_DEVICE_BUFFER);
    edu_mmio_write64(EDU_REG_DMA_COUNT, EDU_TRANSFER_BYTES);
    edu_mmio_write64(EDU_REG_DMA_COMMAND, EDU_DMA_START);
    edu_wait_transfer();
    fault_status = vtd_mmio_read32(0x34);
    fault_low = vtd_mmio_read64(0x220);
    fault_high = vtd_mmio_read64(0x228);
    fault_binding = leanos_validate_assigned_edu_fault(
            1, LEANOS_VTD_ASSIGNED_SOURCE, LEANOS_VTD_ASSIGNED_DOMAIN,
            LEANOS_VTD_ASSIGNED_GENERATION, 2 * PAGE_BYTES, 1,
            fault_status, fault_low, fault_high);
    if (fault_binding != 0) {
        serial_puts("LEANOS/21 VTD-UNMAPPED-FAULT binding=");
        serial_u64(fault_binding);
        serial_puts(" fsts="); serial_u64(fault_status);
        serial_puts(" low="); serial_u64(fault_low);
        serial_puts(" high="); serial_u64(fault_high);
        serial_puts(" result=REJECTED\n");
        fail("vtd-assigned-unmapped-fault-binding");
    }
    if (read_buffer[0] != payload0 || read_buffer[1] != payload1 ||
        write_buffer[0] != secret0 || write_buffer[1] != secret1 ||
        guard_before[0] != guard0 || guard_after[0] != guard1)
        fail("vtd-assigned-unmapped-fault-victim");
    vtd_mmio_write64(0x228, UINT64_C(1) << 63);
    if (vtd_mmio_read32(0x34) != 0)
        fail("vtd-assigned-unmapped-fault-clear");
    if (((volatile uint64_t *)user_a_stack)[0] != subject0 ||
        ((volatile uint64_t *)user_a_stack)[1] != subject1)
        fail("vtd-assigned-protected-subject");
    if (assigned_edu_kernel_record[0] != kernel0 ||
        assigned_edu_kernel_record[1] != kernel1)
        fail("vtd-assigned-protected-kernel");
    if (page_map_level_4_a[0] != protected_page_table_record[0] ||
        page_directory_pointer_a[0] != protected_page_table_record[1] ||
        page_directory_a[0] != protected_page_table_record[2] ||
        page_table_a[user_stack_page] != protected_page_table_record[3])
        fail("vtd-assigned-protected-cpu-tables");
    for (uint64_t word = 0; word < PAGE_BYTES / sizeof(uint64_t); ++word) {
        if (guard_before[word] != (guard0 ^ word) ||
            guard_after[word] != (guard1 ^ word))
            fail("vtd-assigned-protected-guards");
        if (vtd_root_table[word] != leanos_vtd_root_table[word] ||
            vtd_context_table[word] !=
                leanos_vtd_assigned_context_table[word])
            fail("vtd-assigned-protected-vtd-root");
        if (vtd_second_level_root[word] !=
                leanos_vtd_assigned_second_level_root[word] ||
            vtd_second_level_directory[word] !=
                leanos_vtd_assigned_second_level_directory[word] ||
            vtd_second_level_table[word] !=
                leanos_vtd_assigned_second_level_table[word])
            fail("vtd-assigned-protected-vtd-second-level");
    }
    serial_puts("LEANOS/21 VTD-FAULT requester=16 domain=0 generation=1"
        " direction=read iova=8192 reason=6 sid=16"
        " protected=subject,kernel,cpu-page-tables,remapping-tables,guards"
        " records=complete,unchanged"
        " state=current result=PASS\n");

    serial_puts("LEANOS/21 VTD-TRANSFER requester=16 domain=0 generation=1"
        " read-iova=0 write-iova=4096 bytes=16 payload=exact"
        " guards=unchanged fsts=0 result=PASS\n");
}
#endif

#define VTD_REG_VERSION 0x00
#define VTD_REG_CAPABILITY 0x08
#define VTD_REG_EXTENDED_CAPABILITY 0x10
#define VTD_REG_GLOBAL_COMMAND 0x18
#define VTD_REG_GLOBAL_STATUS 0x1c
#define VTD_REG_ROOT_TABLE_ADDRESS 0x20
#define VTD_REG_CONTEXT_COMMAND 0x28
#define VTD_REG_FAULT_STATUS 0x34
#define VTD_GCMD_SET_ROOT_TABLE (UINT32_C(1) << 30)
#define VTD_GCMD_TRANSLATION_ENABLE (UINT32_C(1) << 31)
#define VTD_GSTS_ROOT_TABLE_SET (UINT32_C(1) << 30)
#define VTD_GSTS_TRANSLATION_ENABLED (UINT32_C(1) << 31)
#define VTD_CCMD_INVALIDATE (UINT64_C(1) << 63)
#define VTD_CCMD_GLOBAL (UINT64_C(1) << 61)
#define VTD_IOTLB_INVALIDATE (UINT64_C(1) << 63)
#define VTD_IOTLB_GLOBAL (UINT64_C(1) << 60)
#define VTD_POLL_BOUND 4096u

/* The activation journal accumulates one nibble per completed step, first
   step lowest, matching the generated canonical encoding 0x87654321. */
static uint64_t vtd_journal;
static unsigned vtd_journal_steps;

static void vtd_journal_record(uint64_t tag) {
    vtd_journal |= tag << (4 * vtd_journal_steps);
    ++vtd_journal_steps;
}

static void vtd_wait_global_status(uint32_t mask) {
    for (unsigned attempt = 0; attempt < VTD_POLL_BOUND; ++attempt)
        if (vtd_mmio_read32(VTD_REG_GLOBAL_STATUS) & mask) return;
    fail("vtd-activation-timeout");
}

static void vtd_wait_invalidation(uint64_t offset, uint64_t busy) {
    for (unsigned attempt = 0; attempt < VTD_POLL_BOUND; ++attempt)
        if (!(vtd_mmio_read64(offset) & busy)) return;
    fail("vtd-activation-timeout");
}

static __attribute__((noinline)) void vtd_invalidate_global_iotlb(void) {
    uint64_t extended_capability =
        vtd_mmio_read64(VTD_REG_EXTENDED_CAPABILITY);
    if (extended_capability != LEANOS_VTD_EXPECTED_ECAP)
        fail("vtd-iotlb-extended-capability");
    /* ECAP.IRO is in 16-byte units; IVA is the first 64-bit word and IOTLB
       the second. Keep the derivation and bounded wait shared by boot and the
       assigned-device evidence probe. */
    uint64_t iotlb = ((extended_capability >> 8) & 0x3ff) * 16 + 8;
    vtd_mmio_write64(iotlb, VTD_IOTLB_INVALIDATE | VTD_IOTLB_GLOBAL);
    vtd_wait_invalidation(iotlb, VTD_IOTLB_INVALIDATE);
}

/* Validate the quiescent pinned remapping unit, install the generated
   deny-all tables from scrubbed reserved frames, and enable translation in
   the fixed fail-closed order: validate, scrub, construct, publish,
   invalidate context cache, invalidate IOTLB, enable, verify.  The journal
   nibble sequence and final decoded state must satisfy the generated Lean
   boundary before CPL3. */
static __attribute__((noinline)) void vtd_boot_remap(void) {
    uint64_t version = vtd_mmio_read32(VTD_REG_VERSION);
    uint64_t capability = vtd_mmio_read64(VTD_REG_CAPABILITY);
    uint64_t extended_capability = vtd_mmio_read64(VTD_REG_EXTENDED_CAPABILITY);
    uint64_t global_status = vtd_mmio_read32(VTD_REG_GLOBAL_STATUS);
    uint64_t root_address = vtd_mmio_read64(VTD_REG_ROOT_TABLE_ADDRESS);
    uint64_t fault_status = vtd_mmio_read32(VTD_REG_FAULT_STATUS);
    if (version != LEANOS_VTD_EXPECTED_VERSION) fail("vtd-version");
    if (capability != LEANOS_VTD_EXPECTED_CAP) fail("vtd-capability");
    if (extended_capability != LEANOS_VTD_EXPECTED_ECAP)
        fail("vtd-extended-capability");
    if (global_status != 0) fail("vtd-global-status");
    if (root_address != 0) fail("vtd-root-address");
    if (fault_status != 0) fail("vtd-fault-status");
    if ((uint64_t)vtd_root_table != LEANOS_VTD_ROOT_TABLE_FRAME * PAGE_BYTES ||
        (uint64_t)vtd_context_table !=
            LEANOS_VTD_CONTEXT_TABLE_FRAME * PAGE_BYTES ||
        (uint64_t)vtd_second_level_root !=
            LEANOS_VTD_SECOND_LEVEL_ROOT_FRAME * PAGE_BYTES ||
        (uint64_t)vtd_second_level_directory !=
            LEANOS_VTD_SECOND_LEVEL_DIRECTORY_FRAME * PAGE_BYTES ||
        (uint64_t)vtd_second_level_table !=
            LEANOS_VTD_SECOND_LEVEL_TABLE_FRAME * PAGE_BYTES)
        fail("vtd-plan-frames");
    if (leanos_vtd_root_table[0] !=
        LEANOS_VTD_CONTEXT_TABLE_FRAME * PAGE_BYTES + 1) fail("vtd-plan-root");
    for (uint64_t word = 1; word < 512; ++word)
        if (leanos_vtd_root_table[word] != 0) fail("vtd-plan-root");
    for (uint64_t word = 0; word < 512; ++word)
        if (leanos_vtd_context_table[word] != 0) fail("vtd-plan-context");
    if (LEANOS_VTD_ASSIGNED_REQUESTER != 16 ||
        (uint64_t)vtd_assigned_read_buffer !=
            LEANOS_VTD_ASSIGNED_READ_BUFFER_FRAME * PAGE_BYTES ||
        (uint64_t)vtd_assigned_write_buffer !=
            LEANOS_VTD_ASSIGNED_WRITE_BUFFER_FRAME * PAGE_BYTES ||
        (uint64_t)vtd_assigned_read_buffer -
                (uint64_t)vtd_assigned_guard_before != PAGE_BYTES ||
        (uint64_t)vtd_assigned_write_buffer -
                (uint64_t)vtd_assigned_read_buffer != PAGE_BYTES ||
        (uint64_t)vtd_assigned_guard_after -
                (uint64_t)vtd_assigned_write_buffer != PAGE_BYTES)
        fail("vtd-assigned-buffer-layout");
    if (leanos_validate_assigned_edu_projection(
            1, LEANOS_VTD_ASSIGNED_TOPOLOGY,
            LEANOS_VTD_ASSIGNED_DEVICE, LEANOS_VTD_ASSIGNED_SOURCE,
            LEANOS_VTD_ASSIGNED_GENERATION, LEANOS_VTD_ASSIGNED_DOMAIN,
            LEANOS_VTD_ASSIGNED_DOMAIN_GENERATION, LEANOS_VTD_ASSIGNED_OWNER,
            LEANOS_VTD_ASSIGNED_REQUESTER, LEANOS_VTD_SECOND_LEVEL_ROOT_FRAME,
            LEANOS_VTD_SECOND_LEVEL_DIRECTORY_FRAME,
            LEANOS_VTD_SECOND_LEVEL_TABLE_FRAME,
            LEANOS_VTD_ASSIGNED_READ_BUFFER_FRAME,
            LEANOS_VTD_ASSIGNED_WRITE_BUFFER_FRAME,
            LEANOS_VTD_MODEL_READ_IOVA, LEANOS_VTD_MODEL_READ_LENGTH,
            LEANOS_VTD_MODEL_READ_FRAME,
            LEANOS_VTD_MODEL_READ_FRAME_GENERATION,
            LEANOS_VTD_MODEL_READ_FRAME_OFFSET,
            LEANOS_VTD_MODEL_READ_PERMISSION,
            LEANOS_VTD_MODEL_WRITE_IOVA, LEANOS_VTD_MODEL_WRITE_LENGTH,
            LEANOS_VTD_MODEL_WRITE_FRAME,
            LEANOS_VTD_MODEL_WRITE_FRAME_GENERATION,
            LEANOS_VTD_MODEL_WRITE_FRAME_OFFSET,
            LEANOS_VTD_MODEL_WRITE_PERMISSION) != 0)
        fail("vtd-assigned-authority");
    for (uint64_t word = 0; word < 512; ++word) {
        uint64_t context_low = LEANOS_VTD_ASSIGNED_REQUESTER * 2;
        uint64_t expected_context = word == context_low
            ? LEANOS_VTD_SECOND_LEVEL_ROOT_FRAME * PAGE_BYTES + 1
            : word == context_low + 1
                ? LEANOS_VTD_ASSIGNED_DOMAIN * 256 + 1 : 0;
        uint64_t expected_root = word == 0
            ? LEANOS_VTD_SECOND_LEVEL_DIRECTORY_FRAME * PAGE_BYTES + 3 : 0;
        uint64_t expected_directory = word == 0
            ? LEANOS_VTD_SECOND_LEVEL_TABLE_FRAME * PAGE_BYTES + 3 : 0;
        uint64_t expected_leaf = word == 0
            ? LEANOS_VTD_ASSIGNED_READ_BUFFER_FRAME * PAGE_BYTES + 1
            : word == 1
                ? LEANOS_VTD_ASSIGNED_WRITE_BUFFER_FRAME * PAGE_BYTES + 2 : 0;
        if (leanos_vtd_assigned_context_table[word] != expected_context ||
            leanos_vtd_assigned_second_level_root[word] != expected_root ||
            leanos_vtd_assigned_second_level_directory[word] != expected_directory ||
            leanos_vtd_assigned_second_level_table[word] != expected_leaf)
            fail("vtd-assigned-plan-shape");
    }
    vtd_journal_record(1);
    serial_puts("LEANOS/21 VTD unit=0 mmio=");
    serial_u64(LEANOS_VTD_MMIO_BASE);
    serial_puts(" version="); serial_u64(version);
    serial_puts(" cap="); serial_u64(capability);
    serial_puts(" ecap="); serial_u64(extended_capability);
    serial_puts(" gsts=0 fsts=0 rtaddr=0 stage=pre-activation result=PASS\n");
    serial_puts("LEANOS/21 VTD-PLAN root-frame=");
    serial_u64(LEANOS_VTD_ROOT_TABLE_FRAME);
    serial_puts(" context-frame=");
    serial_u64(LEANOS_VTD_CONTEXT_TABLE_FRAME);
    serial_puts(" root-words=512 context-words=512 present-root-entries=1"
        " present-context-entries=0 translation=disabled deny-all=1"
        " result=PASS\n");

    volatile uint64_t *root = (volatile uint64_t *)vtd_root_table;
    volatile uint64_t *context = (volatile uint64_t *)vtd_context_table;
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
    volatile uint64_t *second_root =
        (volatile uint64_t *)vtd_second_level_root;
    volatile uint64_t *second_directory =
        (volatile uint64_t *)vtd_second_level_directory;
    volatile uint64_t *second_table =
        (volatile uint64_t *)vtd_second_level_table;
#endif
    for (uint64_t word = 0; word < 512; ++word) {
        root[word] = 0;
        context[word] = 0;
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
        second_root[word] = 0;
        second_directory[word] = 0;
        second_table[word] = 0;
#endif
    }
    for (uint64_t word = 0; word < 512; ++word) {
        if (root[word] != 0 || context[word] != 0) fail("vtd-scrub");
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
        if (second_root[word] != 0 || second_directory[word] != 0 ||
            second_table[word] != 0)
            fail("vtd-assigned-scrub");
#endif
    }
    vtd_journal_record(2);

    for (uint64_t word = 0; word < 512; ++word) {
        root[word] = leanos_vtd_root_table[word];
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
        context[word] = leanos_vtd_assigned_context_table[word];
        second_root[word] = leanos_vtd_assigned_second_level_root[word];
        second_directory[word] =
            leanos_vtd_assigned_second_level_directory[word];
        second_table[word] = leanos_vtd_assigned_second_level_table[word];
#else
        context[word] = leanos_vtd_context_table[word];
#endif
    }
    for (uint64_t word = 0; word < 512; ++word) {
        if (root[word] != leanos_vtd_root_table[word] ||
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
            context[word] != leanos_vtd_assigned_context_table[word] ||
            second_root[word] !=
                leanos_vtd_assigned_second_level_root[word] ||
            second_directory[word] !=
                leanos_vtd_assigned_second_level_directory[word] ||
            second_table[word] != leanos_vtd_assigned_second_level_table[word])
            fail("vtd-assigned-construct");
#else
            context[word] != leanos_vtd_context_table[word])
            fail("vtd-construct");
#endif
    }
    vtd_journal_record(3);
    serial_puts("LEANOS/21 VTD-TABLES root-frame=");
    serial_u64(LEANOS_VTD_ROOT_TABLE_FRAME);
    serial_puts(" context-frame=");
    serial_u64(LEANOS_VTD_CONTEXT_TABLE_FRAME);
    serial_puts(" scrub=verified construct=verified root-words=512"
        " context-words=512 result=PASS\n");

    vtd_mmio_write64(VTD_REG_ROOT_TABLE_ADDRESS, LEANOS_VTD_ROOT_TABLE_ADDRESS);
    vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_SET_ROOT_TABLE);
    vtd_wait_global_status(VTD_GSTS_ROOT_TABLE_SET);
    if (vtd_mmio_read64(VTD_REG_ROOT_TABLE_ADDRESS) !=
        LEANOS_VTD_ROOT_TABLE_ADDRESS) fail("vtd-root-publish");
    vtd_journal_record(4);

    vtd_mmio_write64(VTD_REG_CONTEXT_COMMAND,
        VTD_CCMD_INVALIDATE | VTD_CCMD_GLOBAL);
    vtd_wait_invalidation(VTD_REG_CONTEXT_COMMAND, VTD_CCMD_INVALIDATE);
    vtd_journal_record(5);

    vtd_invalidate_global_iotlb();
    vtd_journal_record(6);

    vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, VTD_GCMD_TRANSLATION_ENABLE);
    vtd_wait_global_status(VTD_GSTS_TRANSLATION_ENABLED);
    vtd_journal_record(7);

    uint64_t enabled_status = vtd_mmio_read32(VTD_REG_GLOBAL_STATUS);
    uint64_t enabled_faults = vtd_mmio_read32(VTD_REG_FAULT_STATUS);
    uint64_t enabled_root = vtd_mmio_read64(VTD_REG_ROOT_TABLE_ADDRESS);
    if (enabled_status != LEANOS_VTD_ENABLED_GSTS) fail("vtd-enabled-status");
    if (enabled_faults != 0) fail("vtd-fault-after-enable");
    vtd_journal_record(8);

    if (leanos_validate_vtd_activation(LEANOS_VTD_PLAN_VERSION,
            LEANOS_VTD_TOPOLOGY, version, capability, extended_capability,
            enabled_status, enabled_faults, enabled_root,
            LEANOS_VTD_ROOT_TABLE_ADDRESS, vtd_journal) != 0)
        fail("vtd-generated-activation");
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
    /* The generated authority and complete live table projection have passed,
       and translation is enabled.  Only now may the one assigned function
       decode its MMIO BAR and initiate DMA. */
    const uint16_t assigned_command =
        PCI_COMMAND_MEMORY | PCI_COMMAND_BUS_MASTER;
    uint32_t assigned_bar = pci_config_dword(2, 0, 0x10);
    if ((assigned_bar & EDU_BAR_MASK) != EDU_BAR_BASE ||
        (assigned_bar & ~EDU_BAR_MASK) != 0)
        fail("vtd-assigned-bar");
    pci_config_command(2, 0, assigned_command);
    uint16_t assigned_command_readback =
        (uint16_t)pci_config_dword(2, 0, 0x04);
    if (assigned_command_readback != assigned_command ||
        !q35_live_pci_snapshot.functions[6].assigned)
        fail("vtd-assigned-command");
    if (edu_mmio_read32(EDU_REG_ID) != EDU_EXPECTED_ID)
        fail("vtd-assigned-mmio-identity");
    q35_live_pci_snapshot.functions[6].command_after =
        assigned_command_readback;
    run_assigned_edu_transfers();
    serial_puts("LEANOS/21 VTD-ASSIGN bdf=0:2.0 requester=16 domain=");
    serial_u64(LEANOS_VTD_ASSIGNED_DOMAIN);
    serial_puts(" tables=generated-readback bar=4271898624 mmio-id=16777453"
        " command=6 memory=enabled bus-master=enabled"
        " stage=post-translation result=PASS\n");
#endif
    serial_puts("LEANOS/21 VTD-ACTIVATE order=validate,scrub,construct,publish,"
        "invalidate-context,invalidate-iotlb,enable,verify journal=");
    serial_u64(vtd_journal);
    serial_puts(" gsts="); serial_u64(enabled_status);
    serial_puts(" fsts=0 rtaddr="); serial_u64(enabled_root);
    serial_puts(" generated-result=0 stage=pre-cpl3 result=PASS\n");
}

/* Re-observe the enabled remapping state at every outbound CPL3 gate: the
   exact enabled status, empty fault state, published root pointer, and the
   complete live tables against the generated plan. */
static __attribute__((noinline, noipa)) void verify_vtd_state(void) {
    if (vtd_mmio_read32(VTD_REG_GLOBAL_STATUS) != LEANOS_VTD_ENABLED_GSTS ||
        vtd_mmio_read32(VTD_REG_FAULT_STATUS) != 0 ||
        vtd_mmio_read64(VTD_REG_ROOT_TABLE_ADDRESS) !=
            LEANOS_VTD_ROOT_TABLE_ADDRESS)
        fail("vtd-live-status");
    for (uint64_t word = 0; word < 512; ++word) {
        if (vtd_root_table[word] != leanos_vtd_root_table[word] ||
#ifdef LEANOS_ASSIGNED_EDU_SCENARIO
            vtd_context_table[word] !=
                leanos_vtd_assigned_context_table[word] ||
            vtd_second_level_root[word] !=
                leanos_vtd_assigned_second_level_root[word] ||
            vtd_second_level_directory[word] !=
                leanos_vtd_assigned_second_level_directory[word] ||
            vtd_second_level_table[word] !=
                leanos_vtd_assigned_second_level_table[word])
            fail("vtd-live-assigned-tables");
#else
            vtd_context_table[word] != leanos_vtd_context_table[word])
            fail("vtd-live-tables");
#endif
    }
}

#if LEANOS_RETURN_CORRUPTION_MODE == 26
/* Controlled machine negative only: disable translation after the accepted
   activation so the production outbound status read-back must reject. */
static __attribute__((noinline, noipa)) void inject_vtd_translation_disable(void) {
    vtd_mmio_write32(VTD_REG_GLOBAL_COMMAND, 0);
}
#endif

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

static __attribute__((noinline)) void serial_putc(char value) {
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
replay_extended_or_unknown(const struct oracle_vector *v) {
    if (v->adapter == 18) {
        return leanos_composite_dispatch(
            v->words[0], v->words[1], v->words[2],
            v->words[3], v->words[4], v->words[5]);
    }
    if (v->adapter == 19) {
        return leanos_iotlb_publication_demo(
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
                        ? leanos_boot_consume_exact_projection(
                            v->words[0], v->words[1], v->words[2],
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
                                                            : replay_extended_or_unknown(v);
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

#ifdef LEANOS_FRAME_BUDGET_SCENARIO
static uint64_t frame_budget_leaf(uint64_t page, uint64_t physical_frame) {
    if (page >= BOOT_LEAF_COUNT || physical_frame >= BOOT_LEAF_COUNT)
        fail("frame-budget-mapping-range");
    return physical_frame * PAGE_BYTES | PTE_PRESENT | PTE_WRITABLE |
        PTE_USER | PTE_NX;
}

static __attribute__((noinline)) void
frame_budget_require_publication_authority(void) {
    if (leanos_boot_publish_authority(
            frame_budget_physical_frame,
            frame_budget_rescanned_frame,
            frame_budget_rescan_status,
            frame_budget_rescan_usable,
            frame_budget_rescan_blocked,
            frame_budget_rescan_manifest, 1) !=
        frame_budget_physical_frame + 1)
        fail("frame-budget-publication-authority");
}

static void frame_budget_publish_mapping(
        uint64_t *page_table, uint64_t page, uint64_t physical_frame) {
    if (page >= BOOT_LEAF_COUNT ||
        frame_budget_physical_frame == UINT64_MAX ||
        physical_frame != frame_budget_physical_frame)
        fail("frame-budget-wrong-physical-frame");
    if (physical_frame == frame_budget_boot_published_frame ||
        frame_budget_publication_live)
        fail("frame-budget-double-publication");
    if (page_table[page] & PTE_USER)
        fail("frame-budget-mapping-occupied");
    page_table[page] = frame_budget_leaf(page, physical_frame);
    frame_budget_publication_live = 1;
    __asm__ volatile ("invlpg (%0)" : : "r"(page * PAGE_BYTES) : "memory");
}

/* Retire A's authoritative mapping only under the generated termination
   token.  Because A is inactive while B performs cleanup, a reload of the
   current no-PCID B root supplies the reviewed full non-global flush.  The
   completion token and released-publication bit are written only afterward. */
__attribute__((noinline, used))
static void frame_budget_retire_mapping(
        uint64_t *page_table, uint64_t page, uint64_t physical_frame,
        uint64_t canonical_reply, uint64_t effect_token) {
    uint64_t cr3;
    uint64_t cr4;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
    if (!frame_budget_publication_live || page >= BOOT_LEAF_COUNT ||
        page_table != page_table_a ||
        canonical_reply != UINT64_C(0x444501) ||
        effect_token != LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN ||
        frame_budget_retirement_completion != 0 ||
        (cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_b ||
        (cr4 & (UINT64_C(1) << 17)) != 0 ||
        (page_table[page] & ~(PTE_ACCESSED | PTE_DIRTY)) !=
        frame_budget_leaf(page, physical_frame))
        fail("frame-budget-retire-wrong-mapping");
    ((volatile uint64_t *)page_table)[page] = 0;
    __asm__ volatile ("" ::: "memory");
    __asm__ volatile ("mov %0, %%cr3" :
                      : "r"((uint64_t)page_map_level_4_b) : "memory");
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
    if ((cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_b ||
        page_table[page] != 0)
        fail("frame-budget-retire-flush");
    frame_budget_retirement_completion = effect_token;
    __asm__ volatile ("" ::: "memory");
    frame_budget_publication_live = 0;
}
#endif

uint64_t syscall_handler(uint64_t number, uint64_t arg0, uint64_t arg1,
                         uint64_t arg2, uint64_t saved_cs,
                         uint64_t saved_flags) {
    if ((saved_cs & 3u) != 3u) {
        fail("not-ring3");
    }
#ifdef LEANOS_FRAME_BUDGET_SCENARIO
    if (number >= 20 && number <= 25) {
        uint64_t cr3;
        __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
        uint64_t expected_cr3 = current_subject == 1
            ? (uint64_t)page_map_level_4_a : (uint64_t)page_map_level_4_b;
        if (cr3 != expected_cr3)
            fail("frame-budget-active-address-space");
        if (number == 20 && current_subject == 1) {
            uint64_t prestate = frame_budget_state;
            uint64_t got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_ALLOCATE_A, 10, 0, 0, 0);
            if (got != UINT64_C(0x404101))
                fail("frame-budget-a-allocation");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_A_ALLOCATED;
            frame_budget_user_page = leanos_frame_budget_mapping_page(prestate,
                LEANOS_COMPOSITE_COMMAND_BUDGET_ALLOCATE_A);
            volatile uint8_t *fresh =
                (volatile uint8_t *)(frame_budget_physical_frame * PAGE_BYTES);
            for (unsigned i = 0; i < PAGE_BYTES; ++i)
                fresh[i] = 0;
            for (unsigned i = 0; i < PAGE_BYTES; ++i)
                if (fresh[i] != 0)
                    fail("frame-budget-initial-scrub");
            frame_budget_require_publication_authority();
            frame_budget_publish_mapping(page_table_a, frame_budget_user_page,
                frame_budget_physical_frame);
            serial_puts("LEANOS/20 A-ALLOC subject=1 address-space=1 budget=1 usage=1 object=10 handle=65536 physical-frame=");
            serial_u64(frame_budget_physical_frame);
            serial_puts(" user-page="); serial_u64(frame_budget_user_page);
            serial_puts(" source=generated-mapping prior-publications=0 accepted=1\n");
            return frame_budget_user_page * PAGE_BYTES;
        }
        if (number == 21 && current_subject == 1) {
            uint64_t before_leaf = page_table_a[frame_budget_user_page];
            uint64_t got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_RETRY_A, 11, 1, 0, 0);
            if (got != UINT64_C(0x414201) ||
                before_leaf != page_table_a[frame_budget_user_page])
                fail("frame-budget-a-rejection-mutated");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_A_EXHAUSTED;
            serial_puts("LEANOS/20 A-REJECT subject=1 reason=budgetExhausted budget=1 usage=1 object=none capability=none mapping=none state=unchanged digest=0x4201\n");
            return 1;
        }
        if (number == 22 && current_subject == 1) {
            uint64_t got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_SELECT_B, 0, 0, 0, 0);
            if (got != UINT64_C(0x424301))
                fail("frame-budget-select-b");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_B_SELECTED;
            current_subject = 2;
            serial_puts("LEANOS/20 DISPATCH subject=2 address-space=2 source=generated-current result=PASS\n");
            return 0xfeed;
        }
        if (number == 23 && current_subject == 2) {
            if (arg0 != UINT64_C(0xb2b2f11251a7e55e) ||
                arg1 != UINT64_C(0x030201) || arg2 != UINT64_C(0x51a7))
                fail("frame-budget-b-context-canary");
            serial_puts("LEANOS/20 B-CONTEXT subject=2 source=kernel-owned-fresh registers=15 canaries=fresh result=PASS\n");
            uint64_t got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_ALLOCATE_B, 20, 0, 0, 0);
            if (got != UINT64_C(0x434401))
                fail("frame-budget-b-allocation");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_B_ALLOCATED;
            serial_puts("LEANOS/20 B-ALLOC subject=2 address-space=2 budget=2 usage=1 object=20 handle=131072 peer-a-usage=1 accepted=1\n");
            return UINT64_C(0x20000);
        }
        if (number == 24 && current_subject == 2) {
            if (arg0 != UINT64_C(0x10000))
                fail("frame-budget-stale-handle-word");
            uint64_t effect_token = leanos_frame_budget_invalidation_effect(
                frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_TERMINATE_A);
            uint64_t got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_TERMINATE_A, 0, 0, 0, 0);
            if (got != UINT64_C(0x444501) ||
                effect_token != LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN)
                fail("frame-budget-cleanup");
            frame_budget_retire_mapping(page_table_a, frame_budget_user_page,
                frame_budget_physical_frame, got, effect_token);
            if (frame_budget_retirement_completion != effect_token ||
                frame_budget_publication_live)
                fail("frame-budget-retirement-publication");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_A_TERMINATED;
            serial_puts("LEANOS/20 CLEANUP subject=1 operation=terminate objects=1 mappings=1 capacity-restored=1 repeated-credit=0 effect=flush invalidation=cr3 order=store,cr3,ack,publish checked=1\n");

            volatile uint8_t *reclaimed =
                (volatile uint8_t *)(frame_budget_physical_frame * PAGE_BYTES);
            if (frame_budget_retirement_completion !=
                LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN)
                fail("frame-budget-scrub-before-invalidation");
            for (unsigned i = 0; i < PAGE_BYTES; ++i)
                reclaimed[i] = 0;
            for (unsigned i = 0; i < PAGE_BYTES; ++i)
                if (reclaimed[i] != 0)
                    fail("frame-budget-incomplete-scrub");
            serial_puts("LEANOS/20 SCRUB physical-frame=");
            serial_u64(frame_budget_physical_frame);
            serial_puts(" bytes=4096 complete=1 before-publication=1\n");

            uint64_t prestate = frame_budget_state;
            got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_PUBLISH_FRESH_B, 21, 1, 0, 0);
            if (got != UINT64_C(0x454601))
                fail("frame-budget-fresh-publication");
            if (frame_budget_retirement_completion !=
                LEANOS_FRAME_BUDGET_TERMINATE_FLUSH_TOKEN)
                fail("frame-budget-publish-before-invalidation");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_B_FRESH;
            uint64_t fresh_page = leanos_frame_budget_mapping_page(prestate,
                LEANOS_COMPOSITE_COMMAND_BUDGET_PUBLISH_FRESH_B);
            if (fresh_page != frame_budget_user_page)
                fail("frame-budget-generated-mapping-drift");
            frame_budget_publish_mapping(page_table_b, fresh_page,
                frame_budget_physical_frame);
            serial_puts("LEANOS/20 B-PUBLISH subject=2 object=21 handle=196609 generation=3 physical-frame=");
            serial_u64(frame_budget_physical_frame);
            serial_puts(" user-page="); serial_u64(fresh_page);
            serial_puts(" source=generated-mapping fresh-lifetime=1\n");

            got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_DENY_STALE_A, arg0, 0, 0, 0);
            if (got != UINT64_C(0x464701))
                fail("frame-budget-stale-denial");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_STALE_DENIED;
            serial_puts("LEANOS/20 STALE handle=65536 old-subject=1 fresh-object=21 authorized=0 reason=stale-generation\n");
            return fresh_page * PAGE_BYTES;
        }
        if (number == 25 && current_subject == 2) {
            if (arg0 != 0 || arg1 != 0)
                fail("frame-budget-ring3-canary-visible");

            uint64_t got = leanos_composite_dispatch(frame_budget_state,
                LEANOS_COMPOSITE_COMMAND_BUDGET_COMPLETE, 0, 0, 0, 0);
            if (got != UINT64_C(0x474801))
                fail("frame-budget-complete");
            frame_budget_state = LEANOS_COMPOSITE_STATE_BUDGET_COMPLETE;
            serial_puts("LEANOS/20 CANARY subject=2 origin=cpl3 access=direct first=0 last=0 old=165 denied=1 result=PASS\n");
            serial_puts("LEANOS/20 FINAL status=PASS a-exhausted=1 b-available=1 cleanup=1 scrub=1 fresh=1 stale-denied=1 ring3-reuse=1\n");
            finish(0x10);
        }
        fail("frame-budget-sequence");
    }
#endif
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
    if (number == 19 && current_subject == 2 &&
        page_fault_probe_class == 5) {
        uint64_t cr3;
        __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
        if (arg0 != RUNTIME_MAPPING_BEFORE ||
            arg1 != RUNTIME_MAPPING_ADDRESS || arg2 != RUNTIME_MAPPING_PAGE ||
            (cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_b ||
            runtime_mapping_state != RUNTIME_MAPPING_STATE_BEFORE ||
            (page_table_b[RUNTIME_MAPPING_PAGE] & ~(PTE_ACCESSED | PTE_DIRTY)) !=
                runtime_mapping_leaf(runtime_mapping_frame_before))
            fail("stale-translation-prefill-binding");
        serial_puts("LEANOS/19 TLB-CPL3 event=prefill subject=2 address-space=2 page=7 address=28672 access=read canary=309063438 leaf=present-user result=PASS\n");
        const uint64_t canonical_reply = leanos_composite_dispatch(
            LEANOS_COMPOSITE_STATE_DIRECT_MAPPED,
            LEANOS_COMPOSITE_COMMAND_ACCEPTED_SYSCALL_UNMAP,
            RUNTIME_MAPPING_PAGE, 0, 0, 0);
        runtime_unmap_page7_invlpg(canonical_reply);
        if (runtime_invlpg_publication != canonical_reply)
            fail("stale-translation-unmap-publication");
        serial_puts("LEANOS/19 TLB-CPL3 event=unmap subject=2 address-space=2 page=7 pte=absent effect=page invalidation=invlpg cr3-reload=0 order=store,invlpg,publish result=PASS\n");
        runtime_reuse_page7_frame(canonical_reply);
        if (runtime_reuse_publication != RUNTIME_REUSE_MODEL_REPLY)
            fail("stale-translation-reuse-publication");
        serial_puts("LEANOS/19 TLB-CPL3 event=reuse frame=same old-owner=2 old-lifetime=1 new-owner=1 new-lifetime=2 old-address-space=2 old-page=7 old-pte=absent new-address-space=1 new-page=7 new-pte=present-user scrub=complete canary=308959202 model=post-reuse-old-page-absent order=unmap,invlpg,publish-unmap,scrub,allocate,write-canary,map-new-owner,publish-reuse result=PASS\n");
        return canonical_reply;
    }
    if (number == 20 && current_subject == 1 &&
        page_fault_probe_class == 5) {
        uint64_t cr3;
        __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
        if (arg0 != RUNTIME_MAPPING_AFTER ||
            arg1 != RUNTIME_MAPPING_ADDRESS || arg2 != RUNTIME_MAPPING_PAGE ||
            (cr3 & PTE_ADDRESS) != (uint64_t)page_map_level_4_a ||
            runtime_mapping_state != RUNTIME_MAPPING_STATE_REUSED ||
            runtime_reuse_publication != RUNTIME_REUSE_MODEL_REPLY ||
            runtime_reuse_owner != 1 || runtime_reuse_lifetime != 2 ||
            page_table_b[RUNTIME_MAPPING_PAGE] != 0 ||
            (page_table_a[RUNTIME_MAPPING_PAGE] &
             ~(PTE_ACCESSED | PTE_DIRTY)) !=
                runtime_mapping_leaf(runtime_mapping_frame_before) ||
            runtime_mapping_frame_before[0] != RUNTIME_MAPPING_AFTER)
            fail("stale-translation-new-owner-binding");
        require_runtime_mapping_relation("stale-translation-new-owner-relation");
        serial_puts("LEANOS/19 TLB-CPL3 event=new-owner-read subject=1 address-space=1 page=7 address=28672 access=read frame=same lifetime=2 canary=308959202 old-address-space=2 old-pte=absent result=PASS\n");
        serial_puts("LEANOS/19 FINAL status=PASS prefill=1 accepted-unmap=1 exact-invlpg=1 same-frame-reuse=1 scrub=complete new-owner-cpl3-read=1 replacement-canary=intact stale-access=page-fault old-observation=denied containment=1 incidental-cr3-reload=0\n");
        finish(0x10);
    }
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

static __attribute__((noinline)) void check_original_frame(
    const uint64_t *frame, uint64_t original_rip, uint64_t original_flags,
    uint64_t original_rsp, uint64_t owner) {
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

static __attribute__((noinline)) void check_initial_b_frame(
    const volatile uint64_t *frame) {
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
#ifdef LEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION
    if (page_fault_probe_class == 5) {
        uint64_t cr3;
        __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
        if (transition->result != 1 ||
            snapshot->error != 4 ||
            snapshot->rip !=
                (uint64_t)user_b_stale_translation_fault_instruction ||
            snapshot->fault_address != RUNTIME_MAPPING_ADDRESS ||
            snapshot->fault_page != RUNTIME_MAPPING_PAGE ||
            snapshot->access != 0 || snapshot->protection != 0 ||
            snapshot->user != 1 || snapshot->current_subject != 2 ||
            snapshot->active_address_space != 2 ||
            snapshot->active_cr3 != (uint64_t)page_map_level_4_b ||
            cr3 != (uint64_t)page_map_level_4_b ||
            page_table_b[RUNTIME_MAPPING_PAGE] != 0 ||
            runtime_mapping_state != RUNTIME_MAPPING_STATE_REUSED ||
            runtime_invlpg_publication !=
                LEANOS_COMPOSITE_REPLY_PAGE_UNMAPPED ||
            runtime_reuse_publication != RUNTIME_REUSE_MODEL_REPLY ||
            runtime_reuse_owner != 1 || runtime_reuse_lifetime != 2 ||
            (page_table_a[RUNTIME_MAPPING_PAGE] &
             ~(PTE_ACCESSED | PTE_DIRTY)) !=
                runtime_mapping_leaf(runtime_mapping_frame_before) ||
            runtime_mapping_frame_before[0] != RUNTIME_MAPPING_AFTER)
            fail("stale-translation-fault-binding");
        serial_puts("LEANOS/19 TLB-CPL3 event=denial vector=14 error=4 origin=cpl3 hardware=1 direct-call=0 subject=2 address-space=2 cr2=28672 page=7 access=read protection=0 pte=absent replacement-owner=1 replacement-lifetime=2 replacement-canary=308959202 replacement-canary-intact=1 route=contain handoff=new-owner cr3-reload-since-unmap=0 result=PASS\n");
        current_subject = 1;
        return 3;
    }
#endif
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
    uint64_t expected_leaf =
        user && snapshot.fault_page < BOOT_LEAF_COUNT ?
            expected_boot_leaf((unsigned)active_address_space,
                               snapshot.fault_page) : 0;
    const uint64_t runtime_leaf_relation =
        !user || checked_runtime_leaf((unsigned)active_address_space,
                                      snapshot.fault_page, &expected_leaf);
    const uint64_t report_agrees = !user ||
        (root != 0 && runtime_leaf_relation &&
         decoded_root_matches((unsigned)active_address_space,
                              root, pdpt, pd, pt, 0));
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
#ifdef LEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION
            : page_fault_probe_class == 5
            ? user &&
              snapshot.fault_address == RUNTIME_MAPPING_ADDRESS &&
              snapshot.fault_page == RUNTIME_MAPPING_PAGE &&
              snapshot.error == 4 && snapshot.access == 0 &&
              snapshot.protection == 0 &&
              snapshot.rip ==
                  (uint64_t)user_b_stale_translation_fault_instruction
#endif
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
        page_fault_probe_class == 5 ? 0 : saved_context_owner_b,
        page_fault_probe_class == 5 ? 0 : saved_context_owner_b);
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
#elif defined(LEANOS_FRAME_BUDGET_SCENARIO)
    serial_puts("LEANOS/20 BOOT target=x86_64-q35 subjects=2 schedule=frame-budget-v2 budgets=a:1,b:2 controls=wp,smep,smap\n");
#elif defined(LEANOS_EXTENDED_STATE_SCENARIO)
    serial_puts(extended_state_probe_class >= 5
        ? "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fast-entry-denial controls=wp,smep,smap,em,mp,ts,sce-off\n"
        : "LEANOS/13 BOOT target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts\n");
#elif defined(LEANOS_FAULT_CONTAINMENT_SCENARIO)
    serial_puts(page_fault_probe_class == 5
        ? "LEANOS/19 BOOT target=x86_64-q35 subjects=2 schedule=stale-translation-denial probe=cpl3-unmap-read contract=v1 controls=wp,smep,smap,pcid-off\n"
        : page_fault_probe_class == 4
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
    check_runtime_mapping_invalidation();

    vtd_boot_remap();

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
#elif defined(LEANOS_FRAME_BUDGET_SCENARIO)
    current_subject = 1;
    activate_user_address_space(page_map_level_4_a);
    check_selected_root_a();
    serial_puts("LEANOS/20 ENTER subject=1 address-space=1 cpl=3 budget=1 usage=0\n");
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
    current_subject =
#ifdef LEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION
        page_fault_probe_class == 5 ? 2 :
#endif
        1;
#ifdef LEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION
    if (page_fault_probe_class == 5) {
        arm_cpl3_stale_translation_probe();
        check_selected_root_b();
    } else
#endif
    {
        activate_user_address_space(page_map_level_4_a);
        check_selected_root_a();
    }
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
    serial_puts(page_fault_probe_class == 5
        ? "LEANOS/19 ENTER subject=2 address-space=2 cpl=3 mapping=page7-present-user canary=309063438\n"
        : page_fault_probe_class >= 3
        ? "LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned fatal-only=1\n"
        : "LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned\n");
#ifdef LEANOS_PAGE_FAULT_PROBE_STALE_TRANSLATION
    enter_user(user_b_entry, user_b_stack_top);
#else
    enter_user(user_a_entry, user_a_stack_top);
#endif
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
