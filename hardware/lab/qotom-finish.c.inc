/* Opt-in lab transport, not the canonical absorbing terminal contract.
 * Qotom J1900 / CLBTM210 FADT: 24-bit PM timer 0x408, reset 0xcf9 <- 6.
 * This only recovers paths reaching finish(); it is not a hang watchdog.
 */
static __attribute__((noreturn)) void finish(uint8_t value) {
    (void)value;
    __asm__ volatile ("cli");
    /* Refuse board-specific I/O on an unrelated machine. */
    out32(PCI_CONFIG_ADDRESS, 0x80000000u);
    if (in32(PCI_CONFIG_DATA) == 0x0f008086u) {
        uint32_t previous = in32(0x408u) & 0xffffffu;
        uint64_t elapsed = 0;
        /* ACPI PM timer frequency is 3,579,545 Hz. Poll across wraparound. */
        while (elapsed < 30ull * 3579545ull) {
            uint32_t current = in32(0x408u) & 0xffffffu;
            elapsed += (current - previous) & 0xffffffu;
            previous = current;
            __asm__ volatile ("pause");
        }
        /* Drain the last UART byte before resetting. */
        while ((in8(COM1 + 5) & 0x40u) == 0) {}
        out8(0xcf9u, 6u);
    }
    for (;;) __asm__ volatile ("cli; hlt");
}
