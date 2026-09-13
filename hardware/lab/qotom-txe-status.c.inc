#ifdef LEANOS_QOTOM_PCI_DIAGNOSTIC
#include "qotom-txe-status.h"
#ifdef LEANOS_QOTOM_TXE_BME
static struct qotom_txe_status_observation lab_retained_txe_status;
#endif
/* Earlier native inventory and device stages establish the bound ECAM reader.
 * All prior contexts are disarmed before this read-only stage. */
static __attribute__((noinline)) void lab_capture_txe_status(
        const struct pci_enumeration_snapshot *snapshot) {
    struct qotom_txe_status_observation result={0};
    uint32_t status=7;
#ifdef LEANOS_QOTOM_TXE_BME
    lab_retained_txe_status=(struct qotom_txe_status_observation){0};
#endif
    lab_ecam_window.armed=0;
    if(snapshot->count==16) {
        lab_ecam_window.armed=1;
        status=qotom_collect_txe_status(qotom_ecam_read,&lab_ecam_reader,
            &snapshot->headers[4],&result);
    }
    lab_ecam_window.armed=0;
    serial_puts("LEANOS-LAB/1 TXE-STATUS profile=qotom-txe-status-v1 index=4 status=");serial_u64(status);
    serial_puts(" firmware0=");serial_u64(result.firmware0);
    serial_puts(" firmware1=");serial_u64(result.firmware1);serial_putc('\n');
    if(status!=QOTOM_TXE_OK)pre_admission_fail("qotom-txe-status");
#ifdef LEANOS_QOTOM_TXE_BME
    lab_retained_txe_status=result;
#endif
}
#endif
