#include "qotom-xhci-operational-arm.h"
static __attribute__((noreturn)) void lab_xhci_operational_fault(void *opaque);
static struct lab_xhci_operational_window lab_xhci_operational_reader={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load32=lab_ecam_native_load32,.fault=lab_xhci_operational_fault
};
static void lab_xhci_operational_disarm(void) {
    lab_xhci_operational_reader.armed=0;lab_xhci_smi_disarm();
}
static __attribute__((noreturn)) void lab_xhci_operational_fault(void *opaque) {
    (void)opaque;lab_xhci_operational_disarm();pre_admission_fail("qotom-xhci-operational");
}
#ifdef LEANOS_QOTOM_XHCI_BME
#include "qotom-xhci-bme.c.inc"
#endif
static __attribute__((noinline)) void lab_observe_xhci_operational(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,const struct qotom_xhci_legacy *legacy,
        const struct qotom_xhci_smi_result *smi) {
    struct qotom_xhci_operational result={0};
    uint32_t status=9; /* 9 capability arm, 10 extended arm, 11 operational arm. */
    lab_xhci_operational_disarm();
    if(lab_xhci_arm(&lab_xhci_reader,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=10;
        if(lab_xhci_ext_arm(&lab_xhci_ext_reader,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,caps)) {
            lab_ecam_window.armed=1;status=11;
            if(lab_xhci_operational_arm(&lab_xhci_operational_reader,view,lab_ecam_tables,
                    lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,caps,
                    QOTOM_XHCI_SMI_OBSERVED,smi)) {
                status=qotom_collect_xhci_operational(qotom_ecam_read,&lab_ecam_reader,
                    lab_xhci_window_read,&lab_xhci_reader,lab_xhci_ext_window_read,&lab_xhci_ext_reader,
                    lab_xhci_operational_window_read,&lab_xhci_operational_reader,header,caps,legacy,
                    QOTOM_XHCI_SMI_OBSERVED,smi,&result);
            }
        }
    }
    lab_xhci_operational_disarm();
    serial_puts("LEANOS-LAB/1 XHCI-OPERATIONAL profile=qotom-xhci-operational-v1 index=3 status=");serial_u64(status);
    serial_puts(" sampled=");serial_u64(result.status_before);
    serial_puts(" command=");serial_u64(result.command);
    serial_puts(" final=");serial_u64(result.status_after);serial_putc('\n');
    if(status!=QOTOM_XHCI_OPERATIONAL_OK)pre_admission_fail("qotom-xhci-operational");
#ifdef LEANOS_QOTOM_XHCI_BME
    lab_disable_xhci_bme(view,header,caps,legacy,smi,&result);
#endif
}
