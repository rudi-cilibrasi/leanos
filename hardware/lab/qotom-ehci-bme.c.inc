#include "qotom-ehci-bme-arm.h"
static __attribute__((noreturn)) void lab_bme_fault(void *opaque);
static int lab_bme_store16(void *opaque,uint64_t address,uint16_t value) {
    (void)opaque;
    __asm__ volatile ("" ::: "memory");
    *(volatile uint16_t *)(uintptr_t)address=value;
    __asm__ volatile ("" ::: "memory");
    return 1;
}
static struct lab_ehci_bme_window lab_bme_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_bme_fault
};
static void lab_bme_disarm(void) {
    lab_bme_writer.armed=0;lab_operational_reader.armed=0;
    lab_smi_writer.armed=0;lab_handoff_disarm();
}
static __attribute__((noreturn)) void lab_bme_fault(void *opaque) {
    (void)opaque;lab_bme_disarm();pre_admission_fail("qotom-ehci-bme");
}
static void lab_disable_ehci_bme(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        const struct qotom_ehci_smi_result *smi,
        const struct qotom_ehci_operational *prior) {
    struct qotom_ehci_bme_result result={0};
    uint32_t status=9; /* Local read / operational / write-arm failures: 9..11. */
    lab_bme_disarm();
    if(lab_ehci_arm(&lab_ehci_window,view,lab_ecam_tables,lab_ecam_table_count,
                   (uintptr_t)lab_ecam_aperture,header)) {
        lab_ecam_window.armed=1;status=10;
        if(lab_ehci_operational_arm(&lab_operational_reader,view,lab_ecam_tables,
                lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,caps,
                QOTOM_EHCI_SMI_OBSERVED,smi)) {
            status=11;
            if(lab_ehci_bme_arm(&lab_bme_writer,view,lab_ecam_tables,lab_ecam_table_count,
                    (uintptr_t)lab_ecam_aperture,header,caps,QOTOM_EHCI_SMI_OBSERVED,smi,
                    QOTOM_EHCI_OPERATIONAL_OK,prior)) {
                status=qotom_clear_ehci_bme(qotom_ecam_read,&lab_ecam_reader,
                    lab_ehci_window_read,&lab_ehci_window,
                    lab_ehci_operational_window_read,&lab_operational_reader,
                    lab_ehci_bme_window_write,&lab_bme_writer,header,caps,
                    QOTOM_EHCI_SMI_OBSERVED,smi,QOTOM_EHCI_OPERATIONAL_OK,prior,&result);
            }
        }
    }
    lab_bme_disarm();
    serial_puts("LEANOS-LAB/1 EHCI-BME profile=qotom-bme-v1 index=10 status=");serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.attempted);
    serial_puts(" before=");serial_u64(result.before_command);
    serial_puts(" after=");serial_u64(result.after_command);serial_putc('\n');
    if(status!=QOTOM_EHCI_BME_OK)pre_admission_fail("qotom-ehci-bme");
}
