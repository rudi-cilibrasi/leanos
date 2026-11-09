/* The memory BAR whose pages a lab device program's MMIO window maps
 * (hardware/lab/qotom-wifi.c.inc: the program run and the device stream).
 *
 * Each leaf of the window maps one whole 4 KiB page, the first at the BAR's
 * base, so the base must be page-aligned. A base aligned only to a smaller
 * window would put bit 11 or below into the leaf, where bits 9 to 11 are
 * ignored rather than address bits: the leaf would map the page below the
 * device's registers, and the program would reach memory that is not its
 * device's. The mapped pages must also lie wholly in the PCI hole: at or
 * above 2 GiB and below the I/O APIC at 0xfec00000, with the local APIC and
 * the firmware above it. */
#ifndef LEANOS_QOTOM_LAB_BAR_H
#define LEANOS_QOTOM_LAB_BAR_H
#include <stdint.h>

#define LAB_DEV_BAR_HOLE_BASE UINT32_C(0x80000000)
#define LAB_DEV_BAR_HOLE_END UINT32_C(0xfec00000)

/* 1 when `raw`, a BAR's configuration dword, with `upper` the next BAR's (the
   upper half of a 64-bit BAR, or 0), is a non-prefetchable memory BAR, 32-bit
   (type 0) or 64-bit (type 4, with a zero upper half), whose base is
   page-aligned and aligned to `window`, and whose `pages` pages from the base
   end at or below LAB_DEV_BAR_HOLE_END; else 0. */
static inline int lab_dev_bar_admitted(uint32_t raw, uint32_t upper,
                                       uint32_t window, uint32_t pages) {
    const uint32_t type = raw & 0xfu;
    const uint32_t base = raw & ~UINT32_C(0xf);
    if (type != 0 && !(type == 4 && upper == 0)) return 0;
    if ((base & 4095u) != 0 || (base & (window - 1u)) != 0) return 0;
    if (base < LAB_DEV_BAR_HOLE_BASE || base >= LAB_DEV_BAR_HOLE_END) return 0;
    return pages <= (LAB_DEV_BAR_HOLE_END - base) / 4096u;
}

#endif
