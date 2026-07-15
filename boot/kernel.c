#include <stdint.h>
#include "corpus.h"

#define COM1 0x3f8u
#define DEBUG_EXIT 0xf4u

extern uint64_t leanos_boot_transition(uint64_t state, uint64_t command);
extern uint64_t leanos_syscall_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t leanos_ipc_demo(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t gdt64[];
extern void load_tss(void);
extern void enter_user(void *, void *);
extern void isr80(void);
extern void isr14(void);
extern char user_a_entry[], user_a_stack_top[], user_b_fault_instruction[];
extern char user_b_fault_recovered[];

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
static unsigned ipc_step;
static uint64_t current_subject = 1;
static struct { uint64_t word0, word1, sender; unsigned full; } mailbox;
static void finish(uint8_t value);

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
                : leanos_ipc_demo(v->words[0], v->words[1], v->words[2], v->words[3]);
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

static void set_gate(unsigned vector, void (*handler)(void), uint8_t attributes) {
    uint64_t address = (uint64_t)handler;
    idt[vector] = (struct idt_entry){ (uint16_t)address, 0x08, 0, attributes,
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
    tss.iomap = sizeof(tss);
    set_gate(14, isr14, 0x8e);
    set_gate(0x80, isr80, 0xee);
    struct descriptor idtr = { sizeof(idt) - 1, (uint64_t)idt };
    __asm__ volatile ("lidt %0" : : "m"(idtr));
    load_tss();
}

uint64_t syscall_handler(uint64_t number, uint64_t arg0, uint64_t arg1,
                         uint64_t arg2, uint64_t saved_cs) {
    if ((saved_cs & 3u) != 3u) {
        fail("not-ring3");
    }
    if (ipc_step == 0 && current_subject == 1 && number == 4 &&
        leanos_ipc_demo(current_subject, number, arg0, arg1) == 0) {
        serial_puts("LEANOS/3 SUBJECT id=1 address-space=1 cpl=3\n");
        serial_puts("LEANOS/3 IPC op=receive subject=1 result=denied reason=missing-receive\n");
        ipc_step = 1;
        return 0;
    }
    if (ipc_step == 1 && current_subject == 1 && number == 3 && arg2 == 99 &&
        !mailbox.full && leanos_ipc_demo(current_subject, number, arg0, arg1) == 1) {
        mailbox.word0 = arg0;
        mailbox.word1 = arg1;
        mailbox.sender = current_subject;
        mailbox.full = 1;
        serial_puts("LEANOS/3 IPC op=send subject=1 result=accepted payload=4c45414e:4f53 supplied-sender=99\n");
        ipc_step = 2;
        return 1;
    }
    if (ipc_step == 2 && current_subject == 1 && number == 254) {
        serial_puts("LEANOS/3 HANDOFF from=1 to=2 address-space=2 cr3=switched\n");
        current_subject = 2;
        ipc_step = 3;
        return 0xfeed;
    }
    if (ipc_step == 3 && current_subject == 2 && number == 3 &&
        leanos_ipc_demo(current_subject, number, arg0, arg1) == 0) {
        serial_puts("LEANOS/3 SUBJECT id=2 address-space=2 cpl=3\n");
        serial_puts("LEANOS/3 IPC op=send subject=2 result=denied reason=missing-send\n");
        ipc_step = 4;
        return 0;
    }
    if (ipc_step == 4 && current_subject == 2 && number == 4 && mailbox.full &&
        mailbox.sender == 1 &&
        leanos_ipc_demo(current_subject, number, mailbox.word0, mailbox.word1) == 2) {
        mailbox.full = 0;
        serial_puts("LEANOS/3 IPC op=receive subject=2 result=delivered sender=1 payload=4c45414e:4f53\n");
        serial_puts("LEANOS/3 IPC supplied-sender=99 trusted=0 capability-transfer=none\n");
        ipc_step = 5;
        return 2;
    }
    if (ipc_step == 6 && current_subject == 2 && number == 255) {
        serial_puts("LEANOS/3 RESUME kernel=1\n");
        serial_puts("LEANOS/3 FINAL status=PASS\n");
        finish(0x10);
    }
    fail("ipc-sequence");
}

uint64_t page_fault_handler(uint64_t error, uint64_t rip, uint64_t saved_cs,
                            uint64_t fault_address) {
    if ((saved_cs & 3u) != 3u || error != 5u ||
        current_subject != 2 || ipc_step != 5 ||
        rip != (uint64_t)user_b_fault_instruction || fault_address != 0u) {
        fail("kernel-fault");
    }
    serial_puts("LEANOS/3 FAULT subject=2 vector=14 class=user-supervisor-access contained=1\n");
    ipc_step = 6;
    return (uint64_t)user_b_fault_recovered;
}

/* The sole boot-reachable Lean runtime primitive. See docs/boot-image.md. */
uint8_t lean_uint64_dec_eq(uint64_t left, uint64_t right) {
    return (uint8_t)(left == right);
}

void kernel_main(void) {
    serial_init();
    serial_puts("LEANOS/3 BOOT target=x86_64-q35 subjects=2 schedule=fixed\n");

    replay_oracle();

    privilege_init();
    enter_user(user_a_entry, user_a_stack_top);
    fail("iret-returned");
}
