#include "qotom-xhci-bme-arm.h"
static __attribute__((noreturn)) void lab_xhci_bme_fault(void *opaque);
static struct lab_xhci_bme_window lab_xhci_bme_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_xhci_bme_fault
};
static void lab_xhci_bme_disarm(void) {
    lab_xhci_bme_writer.armed=0;lab_xhci_operational_disarm();
}
static __attribute__((noreturn)) void lab_xhci_bme_fault(void *opaque) {
    (void)opaque;lab_xhci_bme_disarm();pre_admission_fail("qotom-xhci-bme");
}
static __attribute__((noinline)) void lab_disable_xhci_bme(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,const struct qotom_xhci_legacy *legacy,
        const struct qotom_xhci_smi_result *smi,const struct qotom_xhci_operational *prior) {
    struct qotom_xhci_bme_result result={0};
    uint32_t status=9; /* 9 capability, 10 extended, 11 operational, 12 writer arm. */
    lab_xhci_bme_disarm();
    if(lab_xhci_arm(&lab_xhci_reader,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=10;
        if(lab_xhci_ext_arm(&lab_xhci_ext_reader,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,caps)) {
            lab_ecam_window.armed=1;status=11;
            if(lab_xhci_operational_arm(&lab_xhci_operational_reader,view,lab_ecam_tables,
                    lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,caps,QOTOM_XHCI_SMI_OBSERVED,smi)) {
                status=12;
                if(lab_xhci_bme_arm(&lab_xhci_bme_writer,view,lab_ecam_tables,lab_ecam_table_count,
                        (uintptr_t)lab_ecam_aperture,header,caps,QOTOM_XHCI_SMI_OBSERVED,smi,
                        QOTOM_XHCI_OPERATIONAL_OK,prior)) {
                    status=qotom_clear_xhci_bme(qotom_ecam_read,&lab_ecam_reader,
                        lab_xhci_window_read,&lab_xhci_reader,lab_xhci_ext_window_read,&lab_xhci_ext_reader,
                        lab_xhci_operational_window_read,&lab_xhci_operational_reader,
                        lab_xhci_bme_window_write,&lab_xhci_bme_writer,header,caps,legacy,
                        QOTOM_XHCI_SMI_OBSERVED,smi,QOTOM_XHCI_OPERATIONAL_OK,prior,&result);
                }
            }
        }
    }
    lab_xhci_bme_disarm();
    serial_puts("LEANOS-LAB/1 XHCI-BME profile=qotom-xhci-bme-v1 index=3 status=");serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.attempted);
    serial_puts(" before=");serial_u64(result.before_command);
    serial_puts(" after=");serial_u64(result.after_command);serial_putc('\n');
    if(status!=QOTOM_XHCI_BME_OK)pre_admission_fail("qotom-xhci-bme");
}
