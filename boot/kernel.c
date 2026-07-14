#include <stdint.h>

#define COM1 0x3f8u
#define DEBUG_EXIT 0xf4u

extern uint64_t leanos_boot_transition(uint64_t state, uint64_t command);

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

static void finish(uint8_t value) {
    out8(DEBUG_EXIT, value);
    for (;;) {
        __asm__ volatile ("cli; hlt");
    }
}

/* The sole boot-reachable Lean runtime primitive. See docs/boot-image.md. */
uint8_t lean_uint64_dec_eq(uint64_t left, uint64_t right) {
    return (uint8_t)(left == right);
}

void kernel_main(void) {
    serial_init();
    serial_puts("LEANOS/1 BOOT target=x86_64-q35\n");

    uint64_t accepted = leanos_boot_transition(0, 1);
    serial_puts("LEANOS/1 TRANSITION state=0 command=1 result=");
    serial_putc(accepted == 1 ? '1' : '0');
    serial_putc('\n');

    uint64_t rejected = leanos_boot_transition(0, 7);
    serial_puts("LEANOS/1 TRANSITION state=0 command=7 result=");
    serial_putc(rejected == 0 ? '0' : '1');
    serial_putc('\n');

    if (accepted != 1 || rejected != 0) {
        serial_puts("LEANOS/1 FINAL status=FAIL\n");
        finish(0x11);
    }

    serial_puts("LEANOS/1 FINAL status=PASS\n");
    finish(0x10);
}
