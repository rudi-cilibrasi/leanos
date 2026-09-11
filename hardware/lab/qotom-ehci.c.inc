#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
#include "qotom-ehci-arm.h"
#ifdef LEANOS_QOTOM_EHCI_LEGACY
#include "qotom-ehci-legacy.h"
#endif
static __attribute__((noreturn)) void lab_ehci_fault(void *opaque) {
    (void)opaque;
    pre_admission_fail("qotom-ehci-capabilities");
}
static struct lab_ehci_window lab_ehci_window = {
    .controls = lab_ecam_native_controls, .invalidate = lab_ecam_native_invalidate,
    .load32 = lab_ecam_native_load32, .fault = lab_ehci_fault
};
#ifdef LEANOS_QOTOM_EHCI_HANDOFF
#include "qotom-ehci-handoff.c.inc"
#endif
/* The complete native inventory has already matched. Both readers serialize
 * their temporary mappings through the same private aperture; each restores
 * the identity leaf before returning. No operation overlaps another. */
static void lab_capture_ehci(const struct pci_enumeration_snapshot *snapshot) {
    const struct lab_ecam_root_view view = {
        page_map_level_4_a, page_directory_pointer_a, page_directory_a, page_table_a,
        (uintptr_t)page_map_level_4_a, (uintptr_t)page_directory_pointer_a,
        (uintptr_t)page_directory_a, (uintptr_t)page_table_a
    };
    struct qotom_ehci_capabilities result = {0,0,0};
    uint32_t status = 8; /* Local arm failure, outside collector status range. */
    if (snapshot->count == 16 && lab_ehci_arm(&lab_ehci_window, &view,
            lab_ecam_tables, lab_ecam_table_count, (uintptr_t)lab_ecam_aperture,
            &snapshot->headers[10])) {
        lab_ecam_window.armed = 1;
        status = qotom_collect_ehci_capabilities(qotom_ecam_read, &lab_ecam_reader,
            lab_ehci_window_read, &lab_ehci_window, &snapshot->headers[10], &result);
    }
    lab_ecam_window.armed = 0;
    lab_ehci_window.armed = 0;
    serial_puts("LEANOS-LAB/1 EHCI-CAPS profile=qotom-ehci-v1 index=10 status=");
    serial_u64(status);
    serial_puts(" capbase="); serial_u64(result.capbase);
    serial_puts(" structural="); serial_u64(result.structural);
    serial_puts(" capability="); serial_u64(result.capability); serial_putc('\n');
    if (status != QOTOM_EHCI_OK) pre_admission_fail("qotom-ehci-capabilities");
#ifdef LEANOS_QOTOM_EHCI_LEGACY
    struct qotom_ehci_legacy_snapshot legacy = {0};
    uint32_t legacy_status = 11; /* Separate local rearm failure. */
    if (lab_ehci_arm(&lab_ehci_window, &view, lab_ecam_tables,
            lab_ecam_table_count, (uintptr_t)lab_ecam_aperture, &snapshot->headers[10])) {
        lab_ecam_window.armed = 1;
        legacy_status = qotom_collect_ehci_legacy(qotom_ecam_read, &lab_ecam_reader,
            lab_ehci_window_read, &lab_ehci_window, &snapshot->headers[10], &result, &legacy);
    }
    lab_ecam_window.armed = 0;
    lab_ehci_window.armed = 0;
    serial_puts("LEANOS-LAB/1 EHCI-LEGACY profile=qotom-legacy-v1 index=10 status=");
    serial_u64(legacy_status);
    serial_puts(" count="); serial_u64(legacy.count);
    serial_puts(" offset="); serial_u64(legacy.legacy_offset);
    serial_puts(" control="); serial_u64(legacy.control_status); serial_putc('\n');
    for (uint32_t i = 0; i < legacy.count; ++i) {
        serial_puts("LEANOS-LAB/1 EHCI-EXT index="); serial_u64(i);
        serial_puts(" offset="); serial_u64(legacy.headers[i].offset);
        serial_puts(" raw="); serial_u64(legacy.headers[i].raw); serial_putc('\n');
    }
    if (legacy_status != QOTOM_EHCI_LEGACY_OK) pre_admission_fail("qotom-ehci-legacy");
#ifdef LEANOS_QOTOM_EHCI_HANDOFF
    lab_handoff_ehci(&view,&snapshot->headers[10],&result,&legacy);
#endif
#endif
}
#endif
