/* Lab-only: execute a Lean-authored BCM43224 WiFi program (see
   LeanOS/Wifi/Bytecode.lean and hardware/wifi/wifi-exec.h) on the Qotom.

   The Broadcom BAR0 (16 KiB) is shown through four borrowed identity leaves
   of `page_table_a` covering `lab_wifi_window`; the leaves are replaced by
   uncached (PWT|PCD) device mappings for the program's duration and restored
   afterwards. PCI configuration uses mechanism 1 (CF8/CFC) for 02:00.0 only.
   Delays use the ACPI PM timer at port 0x408 (3.579545 MHz, 24-bit). */

static uint8_t lab_wifi_window[4 * 4096] __attribute__((aligned(16384)));
static uint64_t lab_wifi_saved_leaves[4];

#define LAB_WIFI_BUS 2u
#define LAB_WIFI_DEV 0u
#define LAB_WIFI_FN 0u

static uint32_t lab_wifi_cfg_address(uint32_t off) {
    return UINT32_C(0x80000000) | (LAB_WIFI_BUS << 16) | (LAB_WIFI_DEV << 11) |
           (LAB_WIFI_FN << 8) | (off & 0xfcu);
}

uint32_t wifi_hook_cfg_read32(uint32_t off) {
    out32(0xcf8, lab_wifi_cfg_address(off));
    return in32(0xcfc);
}

void wifi_hook_cfg_write32(uint32_t off, uint32_t value) {
    out32(0xcf8, lab_wifi_cfg_address(off));
    out32(0xcfc, value);
}

static volatile uint8_t *lab_wifi_bar(void) {
    return (volatile uint8_t *)lab_wifi_window;
}

uint32_t wifi_hook_mmio_read32(uint32_t off) {
    return *(volatile uint32_t *)(lab_wifi_bar() + off);
}

uint16_t wifi_hook_mmio_read16(uint32_t off) {
    return *(volatile uint16_t *)(lab_wifi_bar() + off);
}

void wifi_hook_mmio_write32(uint32_t off, uint32_t value) {
    *(volatile uint32_t *)(lab_wifi_bar() + off) = value;
}

void wifi_hook_mmio_write16(uint32_t off, uint16_t value) {
    *(volatile uint16_t *)(lab_wifi_bar() + off) = value;
}

void wifi_hook_delay_us(uint32_t us) {
    /* 3.579545 ticks per microsecond; +1 tick rounds up. */
    uint64_t need = ((uint64_t)us * 3579545u + 999999u) / 1000000u + 1u;
    uint32_t last = in32(0x408) & 0xffffffu;
    uint64_t seen = 0;
    while (seen < need) {
        uint32_t now = in32(0x408) & 0xffffffu;
        seen += (now - last) & 0xffffffu;
        last = now;
    }
}

static void lab_wifi_hex(uint32_t value, unsigned digits) {
    static const char nibble[] = "0123456789abcdef";
    for (unsigned i = digits; i-- > 0;)
        serial_putc(nibble[(value >> (4 * i)) & 0xfu]);
}

void wifi_hook_print(uint32_t tag, uint32_t value) {
    serial_puts("WIFI ");
    lab_wifi_hex(tag, 4);
    serial_puts(" 0x");
    lab_wifi_hex(value, 8);
    serial_putc('\n');
}

static void lab_wifi_invlpg(const void *address) {
    __asm__ volatile ("invlpg (%0)" :: "r"(address) : "memory");
}

static void lab_wifi_run(void) {
    uint32_t id = wifi_hook_cfg_read32(0);
    uint32_t bar0 = wifi_hook_cfg_read32(0x10);
    uint32_t bar1 = wifi_hook_cfg_read32(0x14);
    serial_puts("LEANOS-LAB/1 WIFI-BEGIN id=0x");
    lab_wifi_hex(id, 8);
    serial_puts(" bar0=0x");
    lab_wifi_hex(bar0, 8);
    serial_putc('\n');
    /* Non-prefetchable memory BAR, 32-bit (type 0) or 64-bit (type 2 with a
       zero upper half), 16 KiB aligned, in the PCI hole below 4 GiB. */
    uint32_t type = bar0 & 0xfu;
    bar0 &= ~UINT32_C(0xf);
    if (id != UINT32_C(0x435314e4) || (type != 0 && !(type == 4 && bar1 == 0)) ||
        (bar0 & 0x3fffu) != 0 ||
        bar0 < UINT32_C(0x80000000) || bar0 > UINT32_C(0xfec00000)) {
        serial_puts("LEANOS-LAB/1 WIFI-END status=reject\n");
        return;
    }
    uintptr_t window = (uintptr_t)lab_wifi_window;
    for (unsigned i = 0; i < 4; ++i) {
        uint64_t *leaf = &page_table_a[window / 4096 + i];
        lab_wifi_saved_leaves[i] = *leaf;
        if (*leaf != (((uint64_t)window + 4096u * i) | UINT64_C(0x8000000000000003))) {
            serial_puts("LEANOS-LAB/1 WIFI-END status=leaf-mismatch\n");
            for (unsigned j = 0; j < i; ++j) {
                page_table_a[window / 4096 + j] = lab_wifi_saved_leaves[j];
                lab_wifi_invlpg(lab_wifi_window + 4096 * j);
            }
            return;
        }
        *leaf = ((uint64_t)bar0 + 4096u * i) | UINT64_C(0x800000000000001b);
        lab_wifi_invlpg(lab_wifi_window + 4096 * i);
    }
    uint32_t code = 0;
    int status = wifi_exec(lab_wifi_program, (uint32_t)sizeof lab_wifi_program,
                           0, UINT64_C(4000000000), &code);
    for (unsigned i = 0; i < 4; ++i) {
        page_table_a[window / 4096 + i] = lab_wifi_saved_leaves[i];
        lab_wifi_invlpg(lab_wifi_window + 4096 * i);
    }
    serial_puts("LEANOS-LAB/1 WIFI-END status=");
    serial_u64((uint64_t)status);
    serial_puts(" code=0x");
    lab_wifi_hex(code, 8);
    serial_putc('\n');
}
