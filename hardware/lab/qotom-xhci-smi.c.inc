#include "qotom-xhci-smi-arm.h"
static __attribute__((noreturn)) void lab_xhci_smi_fault(void *opaque);
static struct lab_xhci_smi_window lab_xhci_smi_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store32=lab_smi_store32,.fault=lab_xhci_smi_fault
};
static void lab_xhci_smi_disarm(void) {
    lab_xhci_smi_writer.armed=0;lab_xhci_handoff_disarm();
}
static __attribute__((noreturn)) void lab_xhci_smi_fault(void *opaque) {
    (void)opaque;lab_xhci_smi_disarm();pre_admission_fail("qotom-xhci-smi");
}
#ifdef LEANOS_QOTOM_XHCI_OPERATIONAL
#include "qotom-xhci-operational.c.inc"
#endif
static __attribute__((noinline)) void lab_disable_xhci_smi(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,const struct qotom_xhci_legacy *legacy,
        const struct qotom_xhci_handoff_result *handoff) {
    struct qotom_xhci_smi_result result={0};
    uint32_t status=8; /* 8 capability arm, 9 extended arm, 10 writer arm. */
    lab_xhci_smi_disarm();
    if(lab_xhci_arm(&lab_xhci_reader,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=9;
        if(lab_xhci_ext_arm(&lab_xhci_ext_reader,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,caps)) {
            lab_ecam_window.armed=1;status=10;
            if(lab_xhci_smi_arm(&lab_xhci_smi_writer,view,lab_ecam_tables,
                    lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,caps,
                    QOTOM_XHCI_LEGACY_OK,legacy,QOTOM_XHCI_HANDOFF_OBSERVED,handoff)) {
                status=qotom_disable_xhci_smi(qotom_ecam_read,&lab_ecam_reader,
                    lab_xhci_window_read,&lab_xhci_reader,lab_xhci_ext_window_read,&lab_xhci_ext_reader,
                    lab_xhci_smi_window_write,&lab_xhci_smi_writer,header,caps,legacy,
                    QOTOM_XHCI_HANDOFF_OBSERVED,handoff,&result);
            }
        }
    }
    lab_xhci_smi_disarm();
    serial_puts("LEANOS-LAB/1 XHCI-SMI profile=qotom-xhci-smi-v1 index=3 status=");serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.write_attempted);
    serial_puts(" before=");serial_u64(result.before_control);
    serial_puts(" after=");serial_u64(result.after_control);serial_putc('\n');
    if(status!=QOTOM_XHCI_SMI_OBSERVED)pre_admission_fail("qotom-xhci-smi");
#ifdef LEANOS_QOTOM_XHCI_OPERATIONAL
    lab_observe_xhci_operational(view,header,caps,legacy,&result);
#endif
}
