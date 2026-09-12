#include "qotom-ahci-port-arm.h"
static __attribute__((noreturn)) void lab_ahci_port_fault(void *opaque) {
    (void)opaque;pre_admission_fail("qotom-ahci-port");
}
static struct lab_ahci_port_window lab_ahci_port_window={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .load32=lab_ecam_native_load32,.fault=lab_ahci_port_fault
};
static __attribute__((noinline)) void lab_capture_ahci_port(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_header *header,
        const struct qotom_ahci_capabilities *prior) {
    struct qotom_ahci_port result={0};
    uint32_t status=8;
    if(lab_ahci_arm(&lab_ahci_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture,header)) {
        status=9;
        if(lab_ahci_port_arm(&lab_ahci_port_window,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,QOTOM_AHCI_OK,prior)) {
            lab_ecam_window.armed=1;
            status=qotom_collect_ahci_port(qotom_ecam_read,&lab_ecam_reader,
                lab_ahci_window_read,&lab_ahci_window,lab_ahci_port_window_read,&lab_ahci_port_window,
                header,QOTOM_AHCI_OK,prior,&result);
        }
    }
    lab_ecam_window.armed=0;lab_ahci_window.armed=0;lab_ahci_port_window.armed=0;
    serial_puts("LEANOS-LAB/1 AHCI-PORT profile=qotom-ahci-port-v1 index=2 port=1 status=");serial_u64(status);
    serial_puts(" command-before=");serial_u64(result.command_before);
    serial_puts(" interrupt=");serial_u64(result.interrupt_enable);
    serial_puts(" task-file=");serial_u64(result.task_file);
    serial_puts(" sata-status=");serial_u64(result.sata_status);
    serial_puts(" active=");serial_u64(result.active);
    serial_puts(" issued=");serial_u64(result.issued);
    serial_puts(" command-after=");serial_u64(result.command_after);serial_putc('\n');
    if(status!=QOTOM_AHCI_PORT_OK)pre_admission_fail("qotom-ahci-port");
}
