#include <stdint.h>
#include "corpus.h"

#define COM1 0x3f8u
#define DEBUG_EXIT 0xf4u

extern uint64_t leanos_boot_transition(uint64_t state, uint64_t command);
extern uint64_t leanos_syscall_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_ipc_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_preemption_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_boot_allocation_check(uint64_t, uint64_t, uint64_t,
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
extern void isr14(void);
extern void isr32(void);
extern void run_double_fault_probe(void);
extern char user_a_entry[], user_a_stack_top[];
extern char user_a_stack[];
extern char wp_probe_instruction[], wp_probe_recovered[], wp_probe_target[];
extern char smep_probe_recovered[];
extern char __boot_image_start[], __boot_image_end[];
extern char __df_ist_stack_start[], __df_ist_stack_end[];

#define MULTIBOOT2_RUNTIME_MAGIC 0x36d76289u
#define BOOT_ACCESSIBLE_LIMIT (16u * 1024u * 1024u)
#define MAX_HANDOFF_BYTES 65536u
#define MAX_MMAP_ENTRIES 128u
#define PAGE_BYTES 4096u

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
static uint64_t current_subject = 1;
static unsigned timer_accepted;
static unsigned supervisor_probe;
static uint8_t copy_buffer[16];
static unsigned copy_step;
static void finish(uint8_t value);
static __attribute__((noreturn)) void fail(const char *reason);
static void serial_puts(const char *text);
static void serial_putc(char value);

static void serial_u64(uint64_t value) {
    char digits[21]; unsigned length = 0;
    if (value == 0) { serial_putc('0'); return; }
    while (value != 0) { digits[length++] = (char)('0' + value % 10); value /= 10; }
    while (length != 0) serial_putc(digits[--length]);
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
                    : leanos_boot_allocation_check(v->words[0], v->words[1], v->words[2],
                        v->words[3], v->words[4]);
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
        serial_puts("LEANOS/5 FINAL status=PASS ticks=1\n");
        finish(0x10);
    }
    if (number == 3) fail("register-canary");
    fail("ipc-sequence");
}

void timer_handler(uint64_t saved_cs) {
    /* Mask IRQ0 before acknowledging it: duplicate ticks cannot enter the
       protocol.  The PIC/PIT bridge is trusted and documented in ADR 0005. */
    out8(0x21, 0xff);
    out8(0x20, 0x20);
    if ((saved_cs & 3u) != 3u || current_subject != 1 ||
        preemption_step != 1 || timer_accepted != 0) fail("timer-context");
    uint64_t modeled = leanos_preemption_demo(32, current_subject, 2, 1);
    uint64_t next_subject = modeled & 0xffffffffu;
    uint64_t next_address_space = modeled >> 32;
    if (next_subject != 2 || next_address_space != 2) fail("modeled-tick");
    timer_accepted = 1;
    serial_puts("LEANOS/5 TIMER vector=32 source=pit mode=one-shot origin=cpl3 accepted=1\n");
    serial_puts("LEANOS/5 CONTEXT old-subject=1 old-address-space=1 new-subject=2 new-address-space=2 policy=round-robin\n");
    current_subject = next_subject;
    preemption_step = 2;
}

void switch_complete(void) {
    if (current_subject != 2 || preemption_step != 2 || timer_accepted != 1)
        fail("switch-binding");
    preemption_step = 3;
    serial_puts("LEANOS/5 SWITCH subject=2 address-space=2 cr3=switched stack=restored ticks-masked=1\n");
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
    serial_puts("LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit controls=wp,smep,smap\n");

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
    arm_timer();
    enter_user(user_a_entry, user_a_stack_top);
    fail("iret-returned");
}
