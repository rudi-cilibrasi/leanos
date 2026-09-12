#include "qotom-realtek-bme-arm.h"
#ifdef LEANOS_QOTOM_PCIE_PENDING
static struct qotom_realtek_bme_result lab_retained_realtek_bme[2];
#include "qotom-pcie-pending.c.inc"
#endif
static __attribute__((noreturn)) void lab_realtek_bme_fault(void *opaque);
static struct lab_realtek_bme_window lab_realtek_bme_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_realtek_bme_fault
};
static void lab_realtek_bme_disarm(void) {
    lab_ecam_window.armed=0;lab_realtek_state_window.armed=0;
    lab_realtek_bme_writer.armed=0;
}
static __attribute__((noreturn)) void lab_realtek_bme_fault(void *opaque) {
    (void)opaque;lab_realtek_bme_disarm();pre_admission_fail("qotom-realtek-bme");
}
static __attribute__((noinline)) void lab_capture_realtek_bme(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_snapshot *snapshot) {
#ifdef LEANOS_QOTOM_PCIE_PENDING
    for(unsigned port=0;port<2;++port)
        lab_retained_realtek_bme[port]=(struct qotom_realtek_bme_result){0};
#endif
    for(unsigned port=0;port<2;++port) {
        const unsigned index=13+port*2,bus=1+port*2,bridge=6+port*2;
        struct qotom_realtek_bme_result result={0};
        uint32_t status=9; /* State-window arm; writer-arm rejection is 10. */
        lab_realtek_bme_disarm();
        if(snapshot->count==16 && snapshot->headers[index].bus==bus &&
                lab_realtek_state_arm(&lab_realtek_state_window,view,
                lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
                &snapshot->headers[index])) {
            status=10;
            if(lab_realtek_bme_arm(&lab_realtek_bme_writer,view,
                    lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
                    &snapshot->headers[index],&snapshot->headers[bridge],
                    QOTOM_ROOTPORT_OK,&lab_retained_rootport_bme[port*2],
                    QOTOM_REALTEK_OK,&lab_retained_realtek_state[port])) {
                lab_ecam_window.armed=1;
                status=qotom_clear_realtek_bme(qotom_ecam_read,&lab_ecam_reader,
                    lab_realtek_state_window_read,&lab_realtek_state_window,
                    lab_realtek_bme_window_write,&lab_realtek_bme_writer,
                    &snapshot->headers[index],&snapshot->headers[bridge],
                    &lab_retained_pci_caps[bridge],QOTOM_ROOTPORT_OK,
                    &lab_retained_rootport_bme[port*2],QOTOM_REALTEK_OK,
                    &lab_retained_realtek_state[port],&result);
            }
        }
        lab_realtek_bme_disarm();
        serial_puts("LEANOS-LAB/1 REALTEK-BME profile=qotom-realtek-bme-v1 index=");serial_u64(index);
        serial_puts(" status=");serial_u64(status);
        serial_puts(" attempted=");serial_u64(result.attempted);
        serial_puts(" before=");serial_u64(result.before_command);
        serial_puts(" after=");serial_u64(result.after_command);serial_putc('\n');
        if(status!=QOTOM_REALTEK_BME_OK)pre_admission_fail("qotom-realtek-bme");
#ifdef LEANOS_QOTOM_PCIE_PENDING
        lab_retained_realtek_bme[port]=result;
#endif
    }
#ifdef LEANOS_QOTOM_PCIE_PENDING
    lab_capture_pcie_pending(view,snapshot);
#endif
}
