/* Lab-only: execute Lean-authored device programs (LeanOS/Wifi/Bytecode.lean,
   hardware/wifi/wifi-exec.h) on the Qotom: the BCM43224 WiFi driver and the
   xHCI USB keyboard driver.

   Only version-3 images run: each declares its PCI target and confinement
   policy, the declared policy must lie inside the admitted profile for that
   function below (the Qotom policies proved sane in
   LeanOS/DeviceProgramConfinement.lean), and wifi_exec then enforces it on
   every configuration access and physAddr.

   For each program the target's memory BAR is shown through borrowed
   identity leaves of `page_table_a` covering `lab_dev_window`: the leaves are
   replaced by uncached (PWT|PCD) device mappings for the program's duration
   and restored afterwards. PCI configuration uses mechanism 1 (CF8/CFC) for
   the target function only. Delays use the ACPI PM timer at port 0x408
   (3.579545 MHz, 24-bit). Scratch RAM lives in the identity-mapped image
   below 16 MiB, so its virtual address is its physical (DMA) address. */

#define LAB_DEV_MAX_PAGES 16u
#ifndef LAB_PM_TIMER_PORT
#define LAB_PM_TIMER_PORT 0x408u   /* Qotom; QEMU q35 (ICH9) uses 0x608 */
#endif
static uint8_t lab_dev_window[LAB_DEV_MAX_PAGES * 4096] __attribute__((aligned(65536)));
static uint64_t lab_dev_saved_leaves[LAB_DEV_MAX_PAGES];
static struct wifi_target lab_dev_target;

/* Admitted device-program profiles: the widest policy each function may
   declare. Mirrors `qotomBcm43224Policy` / `qotomXhciPolicy`. */
struct lab_dev_profile {
    uint32_t bus, dev, fn, id;
    struct wifi_policy max;
};
static const struct lab_dev_profile lab_dev_profiles[] = {
#ifdef LAB_Q35_DEVICE_LAB
    /* QEMU q35 device lab: qemu-xhci at 00:02.0 (16 KiB), identity/command
       reads, MEM+BM, DMA; sinks CRCR, DCBAAP, ERSTBA, ERDP in qemu-xhci's
       layout. Mirrors `q35XhciPolicy`. */
    { 0, 2, 0, UINT32_C(0x000d1b36),
      { 1, 1, 0x4000u, UINT64_C(0x3), 0, UINT32_C(0xffff0000), UINT32_C(0x6), 4,
        { 0x58, 0x70, 0x1030, 0x1038 } } },
#endif
    /* BCM43224 at 02:00.0: identity/command reads, the two BAR0 core windows,
       Memory Space set and Bus Master cleared (PIO only), no DMA. */
    { 2, 0, 0, UINT32_C(0x435314e4),
      { 1, 0, 0x4000u, UINT64_C(0x3), (UINT64_C(1) << (0x80 / 4)) | (UINT64_C(1) << (0xAC / 4)),
        UINT32_C(0xffff0004), UINT32_C(0x2), 0, { 0 } } },
    /* xHCI at 00:14.0: identity/command and port-routing mask reads, port
       routing writes, Memory Space and Bus Master, DMA into scratch; the
       CRCR, DCBAAP, ERSTBA and ERDP address registers are sinks. */
    { 0, 20, 0, UINT32_C(0x0f358086),
      { 1, 1, 0x10000u, UINT64_C(0x3) | (UINT64_C(1) << (0xD4 / 4)) | (UINT64_C(1) << (0xDC / 4)),
        (UINT64_C(1) << (0xD0 / 4)) | (UINT64_C(1) << (0xD8 / 4)),
        UINT32_C(0xffff0000), UINT32_C(0x6), 4, { 0x98, 0xB0, 0x2030, 0x2038 } } },
    /* AHCI at 00:13.0 (ABAR, 2 KiB): identity/command reads, no configuration
       writes, Memory Space and Bus Master, DMA into scratch; port 1 PxCLB and
       PxFB are sinks. Mirrors `qotomAhciPolicy`. */
    { 0, 19, 0, UINT32_C(0x0f238086),
      { 1, 1, 0x800u, UINT64_C(0x3), 0, UINT32_C(0xffff0004), UINT32_C(0x6), 2, { 0x180, 0x188 } } },
    /* RTL8168E-VL at 01:00.0 (BAR2, 4 KiB): identity/command reads, no
       configuration writes, Memory Space and Bus Master, DMA into scratch;
       the ring bases and the tally dump address are sinks. Mirrors
       `qotomRtl8168Policy`. */
    { 1, 0, 0, UINT32_C(0x816810ec),
      { 1, 1, 0x1000u, UINT64_C(0x3), 0, UINT32_C(0xffff0004), UINT32_C(0x6), 4,
        { 0x10, 0x20, 0x28, 0xE4 } } },
};

/* The declared policy is present and no wider than the target's profile. */
static int lab_dev_policy_admitted(const struct wifi_target *t, const struct wifi_policy *p) {
    if (!p->present)
        return 0;
    for (unsigned i = 0; i < sizeof lab_dev_profiles / sizeof lab_dev_profiles[0]; ++i) {
        const struct lab_dev_profile *q = &lab_dev_profiles[i];
        if (q->bus != t->bus || q->dev != t->dev || q->fn != t->fn || q->id != t->id)
            continue;
        /* Address sinks restrict: the image must declare every profile sink. */
        for (uint32_t k = 0; k < q->max.sink_count; ++k)
            if (!wifi_is_sink(p, q->max.sinks[k]))
                return 0;
        return p->window <= q->max.window && (p->dma <= q->max.dma) &&
               !(p->cfg_read & ~q->max.cfg_read) && !(p->cfg_write & ~q->max.cfg_write) &&
               !(p->cmd_clear & ~q->max.cmd_clear) && !(p->cmd_set & ~q->max.cmd_set);
    }
    return 0;
}

static uint32_t lab_wifi_cfg_address(uint32_t off) {
    return UINT32_C(0x80000000) | (lab_dev_target.bus << 16) | (lab_dev_target.dev << 11) |
           (lab_dev_target.fn << 8) | (off & 0xfcu);
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
    return (volatile uint8_t *)lab_dev_window;
}

uint32_t wifi_hook_mmio_read32(uint32_t off) {
    return *(volatile uint32_t *)(lab_wifi_bar() + off);
}

uint8_t wifi_hook_mmio_read8(uint32_t off) {
    return *(volatile uint8_t *)(lab_wifi_bar() + off);
}

void wifi_hook_mmio_write8(uint32_t off, uint8_t value) {
    *(volatile uint8_t *)(lab_wifi_bar() + off) = value;
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

uint32_t wifi_hook_phys(uint32_t off) {
    /* Identity-mapped image below 16 MiB: virtual address == bus address. */
    return (uint32_t)(uintptr_t)wifi_scratch + off;
}

void wifi_hook_delay_us(uint32_t us) {
    /* 3.579545 ticks per microsecond; +1 tick rounds up. */
    uint64_t need = ((uint64_t)us * 3579545u + 999999u) / 1000000u + 1u;
    uint32_t last = in32(LAB_PM_TIMER_PORT) & 0xffffffu;
    uint64_t seen = 0;
    while (seen < need) {
        uint32_t now = in32(LAB_PM_TIMER_PORT) & 0xffffffu;
        seen += (now - last) & 0xffffffu;
        last = now;
    }
}

static void lab_wifi_hex(uint32_t value, unsigned digits) {
    static const char nibble[] = "0123456789abcdef";
    for (unsigned i = digits; i-- > 0;)
        serial_putc(nibble[(value >> (4 * i)) & 0xfu]);
}

static void lab_wifi_dotted(uint32_t v) {
    /* Lease words hold network-order bytes in little-endian registers. */
    for (unsigned i = 0; i < 4; ++i) {
        if (i) serial_putc('.');
        serial_u64((v >> (8 * i)) & 0xffu);
    }
}

/* One typed character: printable ASCII as itself, others by name or code. */
static void lab_kbd_render(uint32_t value) {
    if (value == '\n') serial_puts("enter");
    else if (value == '\b') serial_puts("backspace");
    else if (value == '\t') serial_puts("tab");
    else if (value == ' ') serial_puts("space");
    else if (value > 0x20 && value < 0x7f) serial_putc((char)value);
    else { serial_puts("0x"); lab_wifi_hex(value, 2); }
}

void wifi_hook_print(uint32_t tag, uint32_t value) {
    /* Lease records from LeanOS/Wifi/Connect.lean (Tag.leasedIp, router,
       subnet, lease) are also rendered as a readable boot message. */
    if (tag == 0x0E05 || tag == 0x0E07 || tag == 0x0E08) {
        serial_puts(tag == 0x0E05 ? "LEANOS-LAB/1 WIFI-DHCP address=" :
                    tag == 0x0E07 ? "LEANOS-LAB/1 WIFI-DHCP router=" :
                                    "LEANOS-LAB/1 WIFI-DHCP netmask=");
        lab_wifi_dotted(value);
        serial_putc('\n');
    } else if (tag == 0x0E09) {
        serial_puts("LEANOS-LAB/1 WIFI-DHCP lease-seconds=");
        serial_u64(((value & 0xffu) << 24) | ((value & 0xff00u) << 8) |
                   ((value >> 8) & 0xff00u) | (value >> 24));
        serial_putc('\n');
    } else if (tag == 0x0F05) {
        serial_puts("LEANOS-LAB/1 WIFI-PING listening address=");
        lab_wifi_dotted(value);
        serial_putc('\n');
    } else if (tag == 0x0F04) {
        serial_puts("LEANOS-LAB/1 WIFI-PING echo-replies=");
        serial_u64(value);
        serial_putc('\n');
    } else if (tag == 0x2100) {
        /* USB keyboard (LeanOS/Usb/Keyboard.lean): one typed character.
           Printable ASCII is echoed as itself, others by name or code. */
        serial_puts("LEANOS-LAB/1 KBD key=");
        lab_kbd_render(value);
        serial_putc('\n');
        return;
    } else if (tag == 0x2101) {
        serial_puts("LEANOS-LAB/1 KBD ready vendor=0x");
        lab_wifi_hex(value & 0xffffu, 4);
        serial_puts(" product=0x");
        lab_wifi_hex(value >> 16, 4);
        serial_puts(" type-now\n");
    } else if (tag == 0x2103) {
        serial_puts("LEANOS-LAB/1 KBD reports=");
        serial_u64(value);
        serial_putc('\n');
    } else if (tag == 0x2102) {
        serial_puts("LEANOS-LAB/1 KBD session-end keys=");
        serial_u64(value);
        serial_putc('\n');
    }
    serial_puts("WIFI ");
    lab_wifi_hex(tag, 4);
    serial_puts(" 0x");
    lab_wifi_hex(value, 8);
    serial_putc('\n');
}

static void lab_wifi_invlpg(const void *address) {
    __asm__ volatile ("invlpg (%0)" :: "r"(address) : "memory");
}

static void lab_dev_restore(unsigned pages) {
    uintptr_t window = (uintptr_t)lab_dev_window;
    for (unsigned j = 0; j < pages; ++j) {
        page_table_a[window / 4096 + j] = lab_dev_saved_leaves[j];
        lab_wifi_invlpg(lab_dev_window + 4096 * j);
    }
}

#define LAB_DEV_STEP_LIMIT UINT64_C(40000000000)

#ifdef LAB_DEVICE_SERVICE
/* Device service (LeanOS/DeviceCapability.lean, ADR 0022), exercised in the
   lab with ring-0 stand-ins for two subjects. The kernel grants subject 1 the
   capability for the admitted device; `bind` is the admission check above
   plus wifi_start; each `invoke` resumes the bound program for at most
   LAB_SERVICE_BUDGET steps and returns what it yielded (one key) or that the
   budget ran out. A subject without the capability is denied, and so is the
   holder after revocation. */
#define LAB_SERVICE_BUDGET 200000u
static uint32_t lab_service_holder;       /* subject holding the device; 0 = none */

static int lab_service_invoke(struct wifi_vm *vm, uint32_t subject, uint32_t *code) {
    if (subject == 0 || subject != lab_service_holder)
        return -1;
    return wifi_resume(vm, 0, vm->steps + LAB_SERVICE_BUDGET, code);
}

static int lab_dev_execute(const uint8_t *image, uint32_t image_len, uint32_t *code) {
    static struct wifi_vm vm;
    if (wifi_start(&vm, image, image_len))
        return WIFI_BAD_IMAGE;
    lab_service_holder = 1;
    serial_puts("LEANOS-LAB/1 SERVICE grant subject=1 bind=accepted\n");
    if (lab_service_invoke(&vm, 2, code) < 0)
        serial_puts("LEANOS-LAB/1 SERVICE invoke subject=2 denied\n");
    uint64_t invocations = 0;
    int status;
    for (;;) {
        status = lab_service_invoke(&vm, 1, code);
        ++invocations;
        if (status == WIFI_YIELD) {
            serial_puts("LEANOS-LAB/1 SERVICE subject=1 key=");
            lab_kbd_render(*code);
            serial_putc('\n');
        } else if (!(status == WIFI_STEP_LIMIT && vm.steps < LAB_DEV_STEP_LIMIT)) {
            break;
        }
    }
    lab_service_holder = 0;
    serial_puts("LEANOS-LAB/1 SERVICE revoke subject=1 invocations=");
    serial_u64(invocations);
    serial_putc('\n');
    uint32_t ignored;
    if (lab_service_invoke(&vm, 1, &ignored) < 0)
        serial_puts("LEANOS-LAB/1 SERVICE invoke subject=1 denied\n");
    return status;
}
#else
static int lab_dev_execute(const uint8_t *image, uint32_t image_len, uint32_t *code) {
    return wifi_exec(image, image_len, 0, LAB_DEV_STEP_LIMIT, code);
}
#endif

static void lab_dev_program_run(const uint8_t *image, uint32_t image_len) {
    uint32_t hdr = 0;
    struct wifi_policy policy;
    if (wifi_image_header(image, image_len, &lab_dev_target, &policy, &hdr)) {
        serial_puts("LEANOS-LAB/1 WIFI-END status=bad-image\n");
        return;
    }
    if (!lab_dev_policy_admitted(&lab_dev_target, &policy)) {
        serial_puts("LEANOS-LAB/1 WIFI-END status=policy-not-admitted\n");
        return;
    }
    uint32_t id = wifi_hook_cfg_read32(0);
    uint32_t bar0 = wifi_hook_cfg_read32(lab_dev_target.bar);
    uint32_t bar1 = lab_dev_target.bar < 0x24u ? wifi_hook_cfg_read32(lab_dev_target.bar + 4u) : 0;
    serial_puts("LEANOS-LAB/1 WIFI-BEGIN id=0x");
    lab_wifi_hex(id, 8);
    serial_puts(" bar0=0x");
    lab_wifi_hex(bar0, 8);
    serial_putc('\n');
    /* Non-prefetchable memory BAR, 32-bit (type 0) or 64-bit (type 2 with a
       zero upper half), aligned to the window, in the PCI hole below 4 GiB. */
    uint32_t type = bar0 & 0xfu;
    uint32_t pages = (lab_dev_target.window + 4095u) / 4096u;
    bar0 &= ~UINT32_C(0xf);
    if (id != lab_dev_target.id || (type != 0 && !(type == 4 && bar1 == 0)) ||
        pages == 0 || pages > LAB_DEV_MAX_PAGES ||
        (bar0 & (lab_dev_target.window - 1u)) != 0 ||
        bar0 < UINT32_C(0x80000000) || bar0 > UINT32_C(0xfec00000)) {
        serial_puts("LEANOS-LAB/1 WIFI-END status=reject\n");
        return;
    }
    uintptr_t window = (uintptr_t)lab_dev_window;
    for (unsigned i = 0; i < pages; ++i) {
        uint64_t *leaf = &page_table_a[window / 4096 + i];
        lab_dev_saved_leaves[i] = *leaf;
        if (*leaf != (((uint64_t)window + 4096u * i) | UINT64_C(0x8000000000000003))) {
            serial_puts("LEANOS-LAB/1 WIFI-END status=leaf-mismatch\n");
            lab_dev_restore(i);
            return;
        }
        *leaf = ((uint64_t)bar0 + 4096u * i) | UINT64_C(0x800000000000001b);
        lab_wifi_invlpg(lab_dev_window + 4096 * i);
    }
    uint32_t code = 0;
    int status = lab_dev_execute(image, image_len, &code);
    lab_dev_restore(pages);
    serial_puts("LEANOS-LAB/1 WIFI-END status=");
    serial_u64((uint64_t)status);
    serial_puts(" code=0x");
    lab_wifi_hex(code, 8);
    serial_putc('\n');
}

static void lab_wifi_run(void) {
    for (unsigned i = 0; i < lab_dev_program_count; ++i)
        lab_dev_program_run(lab_dev_programs[i], lab_dev_program_lengths[i]);
}

#ifdef LEANOS_QOTOM_IPC_DEVICE_STREAM
/* Qotom device stream (issue #449 stage 3): the canonical Qotom blocking-IPC
   profile hosts the bound program for ring-3 subject 1. Binding happens once,
   after whole-platform admission; each invocation, from subject 1's "next
   key" syscall, maps the device window through borrowed leaves of the root
   the dispatcher runs on (the closed root), resumes the program in budgeted
   slices until it yields one key or halts, and restores the leaves before
   returning. */
#ifndef LAB_SERVICE_BUDGET
#define LAB_SERVICE_BUDGET 200000u
#endif
static struct wifi_vm lab_stream_vm;
static uint64_t *lab_stream_leaf_table;
static uint32_t lab_stream_bar, lab_stream_pages, lab_stream_ended;
static uint64_t lab_stream_invocations;

static __attribute__((noinline, unused)) void lab_stream_bind(uint64_t *leaf_table) {
    uint32_t hdr = 0;
    struct wifi_policy policy;
    if (lab_dev_program_count != 1 ||
        wifi_image_header(lab_dev_programs[0], lab_dev_program_lengths[0],
                          &lab_dev_target, &policy, &hdr) ||
        !lab_dev_policy_admitted(&lab_dev_target, &policy))
        pre_admission_fail("qotom-stream-policy");
    uint32_t id = wifi_hook_cfg_read32(0);
    uint32_t bar0 = wifi_hook_cfg_read32(lab_dev_target.bar);
    uint32_t bar1 = lab_dev_target.bar < 0x24u ? wifi_hook_cfg_read32(lab_dev_target.bar + 4u) : 0;
    uint32_t type = bar0 & 0xfu;
    uint32_t pages = (lab_dev_target.window + 4095u) / 4096u;
    bar0 &= ~UINT32_C(0xf);
    if (id != lab_dev_target.id || (type != 0 && !(type == 4 && bar1 == 0)) ||
        pages == 0 || pages > LAB_DEV_MAX_PAGES ||
        (bar0 & (lab_dev_target.window - 1u)) != 0 ||
        bar0 < UINT32_C(0x80000000) || bar0 > UINT32_C(0xfec00000))
        pre_admission_fail("qotom-stream-bar");
    uintptr_t window = (uintptr_t)lab_dev_window;
    for (unsigned i = 0; i < pages; ++i)
        if ((leaf_table[window / 4096 + i] & ~UINT64_C(0x60)) !=
            (((uint64_t)window + 4096u * i) | UINT64_C(0x8000000000000003)))
            pre_admission_fail("qotom-stream-window");
    if (wifi_start(&lab_stream_vm, lab_dev_programs[0], lab_dev_program_lengths[0]))
        pre_admission_fail("qotom-stream-image");
    lab_stream_leaf_table = leaf_table;
    lab_stream_bar = bar0;
    lab_stream_pages = pages;
    serial_puts("LEANOS-LAB/1 SERVICE grant subject=1 device=0:20.0 bind=accepted policy=admitted\n");
}

/* One invocation for subject 1: 0 once the program has halted. */
static __attribute__((noinline, unused)) uint64_t lab_stream_next_key(void) {
    if (lab_stream_ended || !lab_stream_leaf_table) return 0;
    uintptr_t window = (uintptr_t)lab_dev_window;
    uint64_t *leaves = lab_stream_leaf_table;
    for (unsigned i = 0; i < lab_stream_pages; ++i) {
        lab_dev_saved_leaves[i] = leaves[window / 4096 + i];
        leaves[window / 4096 + i] =
            ((uint64_t)lab_stream_bar + 4096u * i) | UINT64_C(0x800000000000001b);
        lab_wifi_invlpg(lab_dev_window + 4096 * i);
    }
    uint64_t key = 0;
    for (;;) {
        uint32_t code = 0;
        int status = wifi_resume(&lab_stream_vm, 0,
            lab_stream_vm.steps + LAB_SERVICE_BUDGET, &code);
        ++lab_stream_invocations;
        if (status == WIFI_YIELD) { key = code; break; }
        if (status == WIFI_STEP_LIMIT && lab_stream_vm.steps < LAB_DEV_STEP_LIMIT)
            continue;
        lab_stream_ended = 1;
        serial_puts("LEANOS-LAB/1 SERVICE end subject=1 status=");
        serial_u64((uint64_t)status);
        serial_puts(" code=0x");
        lab_wifi_hex(code, 8);
        serial_putc('\n');
        break;
    }
    for (unsigned i = 0; i < lab_stream_pages; ++i) {
        leaves[window / 4096 + i] = lab_dev_saved_leaves[i];
        lab_wifi_invlpg(lab_dev_window + 4096 * i);
    }
    return key;
}
#endif
