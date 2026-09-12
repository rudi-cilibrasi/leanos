#include "qotom-xhci-ext-arm.h"
#include "qotom-xhci-legacy.h"
static __attribute__((noreturn)) void lab_xhci_legacy_fault(void *opaque);
static struct lab_xhci_ext_window lab_xhci_ext_reader={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load32=lab_ecam_native_load32,.fault=lab_xhci_legacy_fault
};
static void lab_xhci_legacy_disarm(void) {
    lab_xhci_ext_reader.armed=0;lab_xhci_reader.armed=0;lab_bme_disarm();
}
static __attribute__((noreturn)) void lab_xhci_legacy_fault(void *opaque) {
    (void)opaque;lab_xhci_legacy_disarm();pre_admission_fail("qotom-xhci-legacy");
}
/* Keep this bounded stage separate from the already large EHCI capture path. */
static __attribute__((noinline)) void lab_capture_xhci_legacy(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps) {
    struct qotom_xhci_legacy result={0};
    uint32_t status=11; /* Capability arm failure; 12 is extended arm failure. */
    lab_xhci_legacy_disarm();
    if(lab_xhci_arm(&lab_xhci_reader,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=12;
        if(lab_xhci_ext_arm(&lab_xhci_ext_reader,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,caps)) {
            lab_ecam_window.armed=1;
            status=qotom_collect_xhci_legacy(qotom_ecam_read,&lab_ecam_reader,
                lab_xhci_window_read,&lab_xhci_reader,
                lab_xhci_ext_window_read,&lab_xhci_ext_reader,header,caps,&result);
        }
    }
    lab_xhci_legacy_disarm();
    serial_puts("LEANOS-LAB/1 XHCI-LEGACY profile=qotom-xhci-legacy-v1 index=3 status=");serial_u64(status);
    serial_puts(" count=");serial_u64(result.count);
    serial_puts(" offset=");serial_u64(result.legacy_offset);
    serial_puts(" control=");serial_u64(result.control_status);serial_putc('\n');
    for(unsigned i=0;i<result.count;++i) {
        serial_puts("LEANOS-LAB/1 XHCI-EXT index=");serial_u64(i);
        serial_puts(" offset=");serial_u64(result.headers[i].offset);
        serial_puts(" raw=");serial_u64(result.headers[i].raw);serial_putc('\n');
    }
    if(status!=QOTOM_XHCI_LEGACY_OK)pre_admission_fail("qotom-xhci-legacy");
}
