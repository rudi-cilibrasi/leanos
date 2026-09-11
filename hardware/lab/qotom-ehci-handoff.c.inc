#include "qotom-ehci-semaphore-arm.h"
#include "qotom-pm-delay.h"
#include "qotom-ehci-handoff.h"
static __attribute__((noreturn)) void lab_handoff_fault(void *opaque);
/* Trusted primitives called only by the separately armed transaction helpers. */
static int lab_handoff_store8(void *opaque,uint64_t address,uint8_t value) {
    (void)opaque;
    __asm__ volatile ("" ::: "memory");
    *(volatile uint8_t *)(uintptr_t)address=value;
    __asm__ volatile ("" ::: "memory");
    return 1;
}
static int lab_handoff_timer_read(void *opaque,uint16_t port,uint32_t *value) {
    (void)opaque;
    if(port!=0x408 || !value)return 0;
    *value=in32(0x408);
    return 1;
}
static struct lab_ehci_semaphore lab_handoff_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store8=lab_handoff_store8,.fault=lab_handoff_fault
};
static struct lab_pm_delay lab_handoff_timer={.read32=lab_handoff_timer_read};
static void lab_handoff_disarm(void) {
    lab_ecam_window.armed=0;lab_ehci_window.armed=0;
    lab_handoff_writer.armed=0;lab_handoff_timer.armed=0;
}
static __attribute__((noreturn)) void lab_handoff_fault(void *opaque) {
    (void)opaque;lab_handoff_disarm();pre_admission_fail("qotom-ehci-handoff");
}
static void lab_handoff_ehci(const struct lab_ecam_root_view *view,
        const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        const struct qotom_ehci_legacy_snapshot *legacy) {
    struct qotom_ehci_handoff_result result={0};
    uint32_t status=11; /* 11 read arm, 12 timer arm, 13 writer arm. */
    lab_handoff_disarm();
    if(lab_ehci_arm(&lab_ehci_window,view,lab_ecam_tables,lab_ecam_table_count,
                   (uintptr_t)lab_ecam_aperture,header)) {
        lab_ecam_window.armed=1;
        status=12;
        if(lab_pm_delay_arm(&lab_handoff_timer,lab_ecam_tables,lab_ecam_table_count,
                            qotom_ecam_read,&lab_ecam_reader)) {
            status=13;
            if(lab_ehci_semaphore_arm(&lab_handoff_writer,view,lab_ecam_tables,
                    lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,header,caps,legacy)) {
                status=qotom_request_ehci_handoff(qotom_ecam_read,&lab_ecam_reader,
                    lab_ehci_window_read,&lab_ehci_window,
                    lab_ehci_semaphore_write,&lab_handoff_writer,
                    lab_pm_delay_wait,&lab_handoff_timer,header,caps,legacy,&result);
            }
        }
    }
    lab_handoff_disarm();
    serial_puts("LEANOS-LAB/1 EHCI-HANDOFF profile=qotom-handoff-v1 index=10 status=");
    serial_u64(status);
    serial_puts(" attempted=");serial_u64(result.write_attempted);
    serial_puts(" polls=");serial_u64(result.polls);
    serial_puts(" support=");serial_u64(result.last_support);
    serial_puts(" control=");serial_u64(result.final_control);serial_putc('\n');
    if(status!=QOTOM_EHCI_HANDOFF_OBSERVED)pre_admission_fail("qotom-ehci-handoff");
}
