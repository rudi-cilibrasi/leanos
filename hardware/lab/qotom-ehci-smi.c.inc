#include "qotom-ehci-smi-arm.h"
static __attribute__((noreturn)) void lab_smi_fault(void *opaque);
static int lab_smi_store32(void *opaque,uint64_t address,uint32_t value) {
    (void)opaque;
    __asm__ volatile ("" ::: "memory");
    *(volatile uint32_t *)(uintptr_t)address=value;
    __asm__ volatile ("" ::: "memory");
    return 1;
}
static struct lab_ehci_smi_window lab_smi_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store32=lab_smi_store32,.fault=lab_smi_fault
};
static __attribute__((noreturn)) void lab_smi_fault(void *opaque) {
    (void)opaque;lab_smi_writer.armed=0;lab_handoff_disarm();
    pre_admission_fail("qotom-ehci-smi");
}
static void lab_disable_ehci_smi(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        const struct qotom_ehci_handoff_result *handoff) {
    struct qotom_ehci_smi_result result={0};
    uint32_t status=8; /* Local read-arm / writer-arm failures: 8 / 9. */
    lab_smi_writer.armed=0;lab_handoff_disarm();
    if(lab_ehci_arm(&lab_ehci_window,view,lab_ecam_tables,lab_ecam_table_count,
                   (uintptr_t)lab_ecam_aperture,header)) {
        lab_ecam_window.armed=1;status=9;
        if(lab_ehci_smi_arm(&lab_smi_writer,view,lab_ecam_tables,lab_ecam_table_count,
                (uintptr_t)lab_ecam_aperture,header,caps,QOTOM_EHCI_HANDOFF_OBSERVED,handoff)) {
            status=qotom_disable_ehci_smi(qotom_ecam_read,&lab_ecam_reader,
                lab_ehci_window_read,&lab_ehci_window,lab_ehci_smi_window_write,&lab_smi_writer,
                header,caps,QOTOM_EHCI_HANDOFF_OBSERVED,handoff,&result);
        }
    }
    lab_smi_writer.armed=0;lab_handoff_disarm();
    serial_puts("LEANOS-LAB/1 EHCI-SMI profile=qotom-smi-v1 index=10 status=");
    serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.write_attempted);
    serial_puts(" before=");serial_u64(result.before_control);
    serial_puts(" after=");serial_u64(result.after_control);serial_putc('\n');
    if(status!=QOTOM_EHCI_SMI_OBSERVED)pre_admission_fail("qotom-ehci-smi");
}
