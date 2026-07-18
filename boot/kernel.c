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
extern uint64_t gdt64[];
extern void load_tss(void);
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
extern void isr8(void);
extern void isr13(void);
extern void isr14(void);
extern void isr32(void);
extern void run_double_fault_probe(void);
extern char user_a_entry[], user_a_stack_top[];
extern char user_a_stack[];
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
extern char __kernel_text_start[], __kernel_text_end[];
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
static uint8_t entry_stack[16384] __attribute__((aligned(16)));
static unsigned preemption_step;
uint64_t current_subject = 1;
static unsigned timer_accepted;
static unsigned blocking_ipc_step;
static unsigned supervisor_probe;
static uint8_t copy_buffer[16];
static unsigned copy_step;
static void finish(uint8_t value);
static __attribute__((noreturn)) void fail(const char *reason);
static void serial_puts(const char *text);
static void serial_putc(char value);
static void serial_u64(uint64_t value);
static void arm_timer(void);
static uint64_t stack_marker(uint64_t stack_pointer);
static void check_cross_bank_negative(void);
static void check_initial_b_frame_negative(void);

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
    default: return "none";
    }
}

/* Controlled negative images corrupt the actual outgoing frame immediately
   before the production validator reads it. Each image must terminate here,
   before the first user instruction or iret completion can be observed. */
static void inject_return_corruption(uint64_t *saved) {
    uint64_t mode = return_corruption_mode;
    if (mode == 0) return;
    if (mode == 12 && !(current_subject == 2 && blocking_ipc_step == 4)) return;
    serial_puts("LEANOS/9 RETURN fixture=");
    serial_puts(return_corruption_name(mode));
    serial_puts(" stage=outgoing-frame result=INJECTED\n");
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
    uint64_t rsp = saved[18], ss = saved[19], cr3;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(cr3));
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

static inline void out8(uint16_t port, uint8_t value) {
    __asm__ volatile ("outb %0, %1" : : "a"(value), "Nd"(port));
}

static inline uint8_t in8(uint16_t port) {
    uint8_t value;
    __asm__ volatile ("inb %1, %0" : "=a"(value) : "Nd"(port));
    return value;
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
                                : leanos_capability_reuse_demo(v->words[0], v->words[1],
                                    v->words[2], v->words[3], v->words[4]);
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
    tss.rsp0 = (uint64_t)(entry_stack + sizeof(entry_stack));
    tss.ist[0] = (uint64_t)__df_ist_stack_end;
    tss.iomap = sizeof(tss);
    *(uint64_t *)__df_ist_stack_start = 0xd0b1efa17badc0deull;
    *(uint64_t *)((uint64_t)__df_ist_stack_end - 128u) =
        0x15a1c0decafef00dull;
    set_gate(8, isr8, 1, 0x8e);
    set_gate(13, isr13, 0, 0x8e);
    set_gate(14, isr14, 0, 0x8e);
    set_gate(32, isr32, 0, 0x8e);
    set_gate(0x80, isr80, 0, 0xee);
    struct descriptor idtr = { sizeof(idt) - 1, (uint64_t)idt };
    __asm__ volatile ("lidt %0" : : "m"(idtr));
    load_tss();
}

uint64_t syscall_handler(uint64_t number, uint64_t arg0, uint64_t arg1,
                         uint64_t arg2, uint64_t saved_cs,
                         uint64_t saved_flags) {
    if ((saved_cs & 3u) != 3u) {
        fail("not-ring3");
    }
    if (blocking_ipc_step == 0 && current_subject == 2 && number == 7) {
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
#ifdef LEANOS_PREEMPTION_SCENARIO
    serial_puts("LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=bounded-two-shot-pit controls=wp,smep,smap\n");
#else
    serial_puts("LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap\n");
#endif

    check_boot_page_tables();

    boot_allocate(multiboot_magic, multiboot_info);

    replay_oracle();

    privilege_init();
#ifdef LEANOS_DOUBLE_FAULT_PROBE
    run_double_fault_probe();
#endif
    enable_smep();
    uint64_t cr0, cr4;
    __asm__ volatile ("mov %%cr0, %0" : "=r"(cr0));
    __asm__ volatile ("mov %%cr4, %0" : "=r"(cr4));
    if ((cr0 & (1ull << 16)) == 0 || (cr4 & (1ull << 20)) == 0 ||
        (cr4 & (1ull << 21)) == 0) {
        fail("supervisor-controls");
    }
    serial_puts("LEANOS/6 CONTROL cr0.wp=1 cr4.smep=1 cr4.smap=1 ac=0 stage=exception-path-ready\n");
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
#ifdef LEANOS_PREEMPTION_SCENARIO
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
