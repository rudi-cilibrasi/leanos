#include "qotom-ehci-operational-arm.h"
static __attribute__((noreturn)) void lab_operational_fault(void *opaque);
static struct lab_ehci_operational_window lab_operational_reader={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load32=lab_ecam_native_load32,.fault=lab_operational_fault
};
static __attribute__((noreturn)) void lab_operational_fault(void *opaque) {
    (void)opaque;lab_operational_reader.armed=0;lab_smi_writer.armed=0;
    lab_handoff_disarm();pre_admission_fail("qotom-ehci-operational");
}
static void lab_observe_ehci_operational(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        const struct qotom_ehci_smi_result *prior) {
    struct qotom_ehci_operational result={0};
    uint32_t status=8; /* Local capability-read / operational-arm failures: 8 / 9. */
    lab_operational_reader.armed=0;lab_handoff_disarm();
    if(lab_ehci_arm(&lab_ehci_window,view,lab_ecam_tables,lab_ecam_table_count,
                   (uintptr_t)lab_ecam_aperture,header)) {
        lab_ecam_window.armed=1;status=9;
        if(lab_ehci_operational_arm(&lab_operational_reader,view,lab_ecam_tables,
                lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,caps,
                QOTOM_EHCI_SMI_OBSERVED,prior)) {
            status=qotom_collect_ehci_operational(qotom_ecam_read,&lab_ecam_reader,
                lab_ehci_window_read,&lab_ehci_window,
                lab_ehci_operational_window_read,&lab_operational_reader,
                header,caps,QOTOM_EHCI_SMI_OBSERVED,prior,&result);
        }
    }
    lab_operational_reader.armed=0;lab_handoff_disarm();
    serial_puts("LEANOS-LAB/1 EHCI-OPERATIONAL profile=qotom-operational-v1 index=10 status=");
    serial_u64(status);
    serial_puts(" command=");serial_u64(result.command);
    serial_puts(" status_register=");serial_u64(result.status);
    serial_puts(" interrupt_enable=");serial_u64(result.interrupt_enable);
    serial_puts(" configured=");serial_u64(result.configured);serial_putc('\n');
    if(status!=QOTOM_EHCI_OPERATIONAL_OK)pre_admission_fail("qotom-ehci-operational");
}
