#include "qotom-rootport-bme-arm.h"
static __attribute__((noreturn)) void lab_rootport_bme_fault(void *opaque);
static struct lab_rootport_bme_window lab_rootport_bme_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_rootport_bme_fault
};
static void lab_rootport_bme_disarm(void) {
    lab_ecam_window.armed=0;lab_rootport_bme_writer.armed=0;
}
static __attribute__((noreturn)) void lab_rootport_bme_fault(void *opaque) {
    (void)opaque;lab_rootport_bme_disarm();pre_admission_fail("qotom-rootport-bme");
}
static __attribute__((noinline)) void lab_capture_rootport_bme(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_snapshot *snapshot) {
    for(unsigned fn=0;fn<4;++fn) {
        struct qotom_rootport_bme_result result={0};
        uint32_t status=8; /* Local count/arm rejection. */
        lab_rootport_bme_disarm();
        if(snapshot->count==16 && lab_rootport_bme_arm(&lab_rootport_bme_writer,view,
                lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
                &snapshot->headers[6+fn],&lab_retained_pcie_device[6+fn])) {
            lab_ecam_window.armed=1;
            status=qotom_clear_rootport_bme(qotom_ecam_read,&lab_ecam_reader,
                lab_rootport_bme_window_write,&lab_rootport_bme_writer,
                &snapshot->headers[6+fn],&lab_retained_pci_caps[6+fn],
                &lab_retained_pcie_device[6+fn],&result);
        }
        lab_rootport_bme_disarm();
        serial_puts("LEANOS-LAB/1 ROOTPORT-BME profile=qotom-rootport-bme-v1 index=");serial_u64(6+fn);
        serial_puts(" status=");serial_u64(status);
        serial_puts(" attempted=");serial_u64(result.attempted);
        serial_puts(" before=");serial_u64(result.before_command);
        serial_puts(" after=");serial_u64(result.after_command);serial_putc('\n');
        if(status!=QOTOM_ROOTPORT_OK)pre_admission_fail("qotom-rootport-bme");
    }
}
