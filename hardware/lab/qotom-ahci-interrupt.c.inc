#include "qotom-ahci-interrupt-arm.h"
static __attribute__((noreturn)) void lab_ahci_interrupt_fault(void *opaque);
static struct lab_ahci_interrupt_window lab_ahci_interrupt_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store32=lab_smi_store32,.fault=lab_ahci_interrupt_fault
};
static void lab_ahci_interrupt_disarm(void) {
    lab_ecam_window.armed=0;lab_ahci_window.armed=0;
    lab_ahci_port_window.armed=0;lab_ahci_interrupt_writer.armed=0;
}
static __attribute__((noreturn)) void lab_ahci_interrupt_fault(void *opaque) {
    (void)opaque;lab_ahci_interrupt_disarm();pre_admission_fail("qotom-ahci-interrupts");
}
static __attribute__((noinline)) void lab_disable_ahci_interrupts(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_header *header,
        const struct qotom_ahci_capabilities *caps,const struct qotom_ahci_port *prior) {
    struct qotom_ahci_interrupt_result result={0};
    uint32_t status=9; /* Global reader, port reader, writer arms: 9,10,11. */
    lab_ahci_interrupt_disarm();
    if(lab_ahci_arm(&lab_ahci_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=10;
        if(lab_ahci_port_arm(&lab_ahci_port_window,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,QOTOM_AHCI_OK,caps)) {
            status=11;
            if(lab_ahci_interrupt_arm(&lab_ahci_interrupt_writer,view,lab_ecam_tables,
                    lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,
                    QOTOM_AHCI_OK,caps,QOTOM_AHCI_PORT_OK,prior)) {
                lab_ecam_window.armed=1;
                status=qotom_disable_ahci_interrupts(qotom_ecam_read,&lab_ecam_reader,
                    lab_ahci_window_read,&lab_ahci_window,lab_ahci_port_window_read,&lab_ahci_port_window,
                    lab_ahci_interrupt_window_write,&lab_ahci_interrupt_writer,
                    header,QOTOM_AHCI_OK,caps,QOTOM_AHCI_PORT_OK,prior,&result);
            }
        }
    }
    lab_ahci_interrupt_disarm();
    serial_puts("LEANOS-LAB/1 AHCI-INTERRUPTS profile=qotom-ahci-interrupts-v1 index=2 status=");serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.write_attempted);
    serial_puts(" before=");serial_u64(result.before_control);
    serial_puts(" after=");serial_u64(result.after_control);serial_putc('\n');
    if(status!=QOTOM_AHCI_INTERRUPTS_OK)pre_admission_fail("qotom-ahci-interrupts");
}
