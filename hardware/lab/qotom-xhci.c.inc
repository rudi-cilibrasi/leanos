#include "qotom-xhci-arm.h"
static __attribute__((noreturn)) void lab_xhci_fault(void *opaque);
static struct lab_xhci_window lab_xhci_reader={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load32=lab_ecam_native_load32,.fault=lab_xhci_fault
};
static __attribute__((noreturn)) void lab_xhci_fault(void *opaque) {
    (void)opaque;lab_xhci_reader.armed=0;lab_bme_disarm();
    pre_admission_fail("qotom-xhci-capabilities");
}
#ifdef LEANOS_QOTOM_XHCI_LEGACY
#include "qotom-xhci-legacy.c.inc"
#endif
static void lab_capture_xhci(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header) {
    struct qotom_xhci_capabilities result={0};
    uint32_t status=8; /* Local arm rejection. */
    lab_xhci_reader.armed=0;lab_bme_disarm();
    if(lab_xhci_arm(&lab_xhci_reader,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        lab_ecam_window.armed=1;
        status=qotom_collect_xhci_capabilities(qotom_ecam_read,&lab_ecam_reader,
            lab_xhci_window_read,&lab_xhci_reader,header,&result);
    }
    lab_xhci_reader.armed=0;lab_bme_disarm();
    serial_puts("LEANOS-LAB/1 XHCI-CAPS profile=qotom-xhci-v1 index=3 status=");serial_u64(status);
    serial_puts(" words=");
    for(unsigned i=0;i<7;++i){if(i)serial_putc(',');serial_u64(result.words[i]);}
    serial_putc('\n');
    if(status!=QOTOM_XHCI_OK)pre_admission_fail("qotom-xhci-capabilities");
#ifdef LEANOS_QOTOM_XHCI_LEGACY
    lab_capture_xhci_legacy(view,header,&result);
#endif
}
