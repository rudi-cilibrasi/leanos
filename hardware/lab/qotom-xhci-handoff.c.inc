#include "qotom-xhci-semaphore-arm.h"
#include "qotom-xhci-handoff.h"
static __attribute__((noreturn)) void lab_xhci_handoff_fault(void *opaque);
static struct lab_xhci_semaphore_window lab_xhci_handoff_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store32=lab_smi_store32,.fault=lab_xhci_handoff_fault
};
static void lab_xhci_handoff_disarm(void) {
    lab_xhci_handoff_writer.armed=0;lab_xhci_legacy_disarm();
}
static __attribute__((noreturn)) void lab_xhci_handoff_fault(void *opaque) {
    (void)opaque;lab_xhci_handoff_disarm();pre_admission_fail("qotom-xhci-handoff");
}
static __attribute__((noinline)) void lab_handoff_xhci(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,const struct qotom_xhci_legacy *legacy) {
    struct qotom_xhci_handoff_result result={0};
    uint32_t status=11; /* 11 capability arm, 12 extended arm, 13 timer, 14 writer. */
    lab_xhci_handoff_disarm();
    if(lab_xhci_arm(&lab_xhci_reader,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=12;
        if(lab_xhci_ext_arm(&lab_xhci_ext_reader,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,caps)) {
            lab_ecam_window.armed=1;status=13;
            if(lab_pm_delay_arm(&lab_handoff_timer,lab_ecam_tables,lab_ecam_table_count,
                    qotom_ecam_read,&lab_ecam_reader)) {
                status=14;
                if(lab_xhci_semaphore_arm(&lab_xhci_handoff_writer,view,lab_ecam_tables,
                        lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,caps,
                        QOTOM_XHCI_LEGACY_OK,legacy)) {
                    status=qotom_request_xhci_handoff(qotom_ecam_read,&lab_ecam_reader,
                        lab_xhci_window_read,&lab_xhci_reader,
                        lab_xhci_ext_window_read,&lab_xhci_ext_reader,
                        lab_xhci_semaphore_window_write,&lab_xhci_handoff_writer,
                        lab_pm_delay_wait,&lab_handoff_timer,header,caps,legacy,&result);
                }
            }
        }
    }
    lab_xhci_handoff_disarm();
    serial_puts("LEANOS-LAB/1 XHCI-HANDOFF profile=qotom-xhci-handoff-v2 index=3 status=");serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.write_attempted);
    serial_puts(" polls=");serial_u64(result.polls);
    serial_puts(" support=");serial_u64(result.last_support);
    serial_puts(" control=");serial_u64(result.final_control);
    serial_puts(" verify=");serial_u64(result.verify_kind);
    serial_puts(" verify-index=");serial_u64(result.verify_index);
    serial_puts(" expected=");serial_u64(result.verify_expected);
    serial_puts(" observed=");serial_u64(result.verify_observed);serial_putc('\n');
    if(status!=QOTOM_XHCI_HANDOFF_OBSERVED)pre_admission_fail("qotom-xhci-handoff");
}
