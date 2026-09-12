#include "qotom-ahci-bme-arm.h"
static __attribute__((noreturn)) void lab_ahci_bme_fault(void *opaque);
static struct lab_ahci_bme_window lab_ahci_bme_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_ahci_bme_fault
};
static void lab_ahci_bme_disarm(void) {
    lab_ahci_interrupt_disarm();lab_ahci_bme_writer.armed=0;
}
static __attribute__((noreturn)) void lab_ahci_bme_fault(void *opaque) {
    (void)opaque;lab_ahci_bme_disarm();pre_admission_fail("qotom-ahci-bme");
}
static __attribute__((noinline)) void lab_clear_ahci_bme(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_header *header,
        const struct qotom_ahci_capabilities *caps,const struct qotom_ahci_port *prior,
        const struct qotom_ahci_interrupt_result *interrupt) {
    struct qotom_ahci_bme_result result={0};
    struct qotom_ahci_capabilities disabled=*caps;disabled.control=interrupt->after_control;
    uint32_t status=9; /* Global reader, port reader, writer arms: 9,10,11. */
    lab_ahci_bme_disarm();
    if(lab_ahci_arm(&lab_ahci_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=10;
        if(lab_ahci_port_arm(&lab_ahci_port_window,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,QOTOM_AHCI_OK,&disabled)) {
            status=11;
            if(lab_ahci_bme_arm(&lab_ahci_bme_writer,view,lab_ecam_tables,
                    lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,
                    QOTOM_AHCI_OK,caps,QOTOM_AHCI_PORT_OK,prior,QOTOM_AHCI_INTERRUPTS_OK,interrupt)) {
                lab_ecam_window.armed=1;
                status=qotom_clear_ahci_bme(qotom_ecam_read,&lab_ecam_reader,
                    lab_ahci_window_read,&lab_ahci_window,lab_ahci_port_window_read,&lab_ahci_port_window,
                    lab_ahci_bme_window_write,&lab_ahci_bme_writer,
                    header,QOTOM_AHCI_OK,caps,QOTOM_AHCI_PORT_OK,prior,QOTOM_AHCI_INTERRUPTS_OK,interrupt,&result);
            }
        }
    }
    lab_ahci_bme_disarm();
    serial_puts("LEANOS-LAB/1 AHCI-BME profile=qotom-ahci-bme-v1 index=2 status=");serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.attempted);
    serial_puts(" before=");serial_u64(result.before_command);
    serial_puts(" after=");serial_u64(result.after_command);serial_putc('\n');
    if(status!=QOTOM_AHCI_BME_OK)pre_admission_fail("qotom-ahci-bme");
}
