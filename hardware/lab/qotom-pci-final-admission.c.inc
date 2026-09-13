#include "qotom-pci-final-admission.h"

static __attribute__((noreturn,noinline)) void lab_capture_pci_final_admission(
        const struct lab_ecam_root_view *view) {
    static struct pci_enumeration_snapshot final_snapshot;
    lab_ecam_window.armed=0;
    if(!lab_ecam_arm(&lab_ecam_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture))
        pre_admission_fail("qotom-pci-final-arm");
    lab_ecam_window.armed=1;
    struct pci_enumeration_result scan=pci_enumerate_segment(
        qotom_ecam_read,&lab_ecam_reader,&final_snapshot);
    lab_ecam_window.armed=0;

    /* Intel 329670-002 describes the host bridge's fixed Command bits and says
     * LPC performs no DMA/bus mastering. The remaining three assumptions have
     * no accepted witness and stay explicitly false. */
    const struct qotom_pci_final_assumptions assumptions={1,1,0,0,0};
    struct qotom_pci_final_result result=qotom_check_pci_final(scan.status,
        &final_snapshot,leanos_qotom_native_pci_header_check,
        leanos_qotom_pci_final_commands,leanos_qotom_pci_final_admission,
        &assumptions);
    serial_puts("LEANOS-LAB/1 PCI-FINAL profile=qotom-pci-final-v1 status=");
    serial_u64(result.status);serial_puts(" index=");serial_u64(result.index);
    serial_puts(" count=");serial_u64(final_snapshot.count);
    serial_puts(" commands-accepted=");serial_u64(result.commands_accepted);
    serial_puts(" assumption-mask=");serial_u64(result.assumption_mask);
    serial_puts(" admitted=");serial_u64(result.admitted);
    serial_puts(" commands=");
    for(unsigned i=0;i<16;++i) {
        if(i)serial_putc(',');
        serial_u64(result.commands[i]);
    }
    serial_puts(" vtd=not-applicable platform-admitted=0\n");
    if(result.status==QOTOM_PCI_FINAL_ASSUMPTIONS)
        pre_admission_fail("qotom-pci-assumptions");
    if(result.status!=QOTOM_PCI_FINAL_MATCH)
        pre_admission_fail("qotom-pci-final");
    pre_admission_fail("qotom-nosmap-pending");
}
