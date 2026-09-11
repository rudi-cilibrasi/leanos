#ifndef LEANOS_LAB_QOTOM_ECAM_MEMORY_H
#define LEANOS_LAB_QOTOM_ECAM_MEMORY_H
#include <stdint.h>

struct lab_ecam_controls {
    uint64_t pat, cr0, cr3, cr4, efer, rflags;
};

/* Necessary local CPU conditions for the lab's four-level, non-PCID aperture.
 * Requires the observed PAT layout (slot0 WB, slot3 UC), paging/write protection,
 * long mode/NXE, and disabled maskable interrupts. No register is changed.
 * This is not firmware/AP exclusion, alias validation, or platform admission. */
static inline int lab_ecam_controls_match(const struct lab_ecam_controls *c,
                                        uint64_t expected_root) {
    const uint64_t required_cr0 = UINT64_C(0x80010001); /* PG, WP, PE */
    const uint64_t forbidden_cr0 = UINT64_C(0x60000000); /* CD, NW */
    const uint64_t forbidden_cr4 = UINT64_C(0x21080); /* PCIDE, LA57, PGE */
    if (!c || !expected_root || expected_root >= UINT64_C(0x1000000) ||
        (expected_root & 4095u) || c->cr3 != expected_root ||
        c->pat != UINT64_C(0x0007040600070406) ||
        (c->cr0 & (required_cr0 | forbidden_cr0)) != required_cr0 ||
        (c->cr4 & (forbidden_cr4 | UINT64_C(0x20))) != UINT64_C(0x20) ||
        (c->efer & UINT64_C(0xd00)) != UINT64_C(0xd00) ||
        (c->rflags & UINT64_C(0x20200))) /* VM, IF */
        return 0;
    return 1;
}

/* Construct only the conventional aligned dword aperture leaf. With the
 * admitted PAT layout, PAT=0/PCD=1/PWT=1 selects UC (not UC-minus). The caller
 * must also establish resource binding, absence of cache aliases, the active
 * root/ancestor shape, leaf ownership, invalidation and terminal-fault policy. */
static inline int lab_ecam_read_leaf(uint64_t address, uint64_t *leaf) {
    if (!leaf || address < UINT64_C(0xe0000000) ||
        address >= UINT64_C(0xf0000000) || (address & 3u) ||
        (address & 4095u) > 252u) return 0;
    *leaf = (address & ~UINT64_C(4095)) | UINT64_C(0x8000000000000019);
    return 1;
}
#endif
