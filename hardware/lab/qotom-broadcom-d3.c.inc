#include "qotom-broadcom-d3-arm.h"

static __attribute__((noreturn)) void lab_broadcom_d3_fault(void *opaque);
static struct lab_broadcom_d3_window lab_broadcom_d3_writer={
    .controls=lab_ecam_native_controls,.invalidate=lab_ecam_native_invalidate,
    .store16=lab_bme_store16,.fault=lab_broadcom_d3_fault
};
static int lab_broadcom_d3_timer_read(void *opaque,uint16_t port,uint32_t *value) {
    (void)opaque;
    if(port!=0x408 || !value)return 0;
    *value=in32(0x408);return 1;
}
static struct lab_pm_delay lab_broadcom_d3_timer={.read32=lab_broadcom_d3_timer_read};
static void lab_broadcom_d3_disarm(void) {
    lab_ecam_window.armed=0;lab_broadcom_d3_writer.armed=0;
    lab_broadcom_d3_writer.stage=0;lab_broadcom_d3_timer.armed=0;
}
static __attribute__((noreturn)) void lab_broadcom_d3_fault(void *opaque) {
    (void)opaque;lab_broadcom_d3_disarm();pre_admission_fail("qotom-broadcom-d3");
}
static __attribute__((noinline)) void lab_capture_broadcom_d3(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_snapshot *snapshot) {
    struct qotom_broadcom_d3_result result={0};
    uint32_t status=12;
    lab_broadcom_d3_disarm();
    if(snapshot->count==16 &&
       lab_broadcom_d3_arm(&lab_broadcom_d3_writer,view,
            lab_ecam_tables,lab_ecam_table_count,(uintptr_t)lab_ecam_aperture,
            &snapshot->headers[14],&snapshot->headers[7],
            &lab_retained_pci_caps[14],&lab_retained_pcie_device[14],
            QOTOM_ROOTPORT_OK,&lab_retained_rootport_bme[1],
            QOTOM_PCIE_PENDING_OK,&lab_retained_pcie_pending[1])) {
        status=13;
        lab_ecam_window.armed=1;
        if(lab_pm_delay_arm(&lab_broadcom_d3_timer,lab_ecam_tables,
                lab_ecam_table_count,qotom_ecam_read,&lab_ecam_reader))
            status=qotom_broadcom_enter_d3hot(qotom_ecam_read,&lab_ecam_reader,
                lab_broadcom_d3_window_write,&lab_broadcom_d3_writer,
                lab_pm_delay_wait,&lab_broadcom_d3_timer,
                &snapshot->headers[14],&snapshot->headers[7],
                &lab_retained_pci_caps[14],&lab_retained_pcie_device[14],
                QOTOM_ROOTPORT_OK,&lab_retained_rootport_bme[1],
                QOTOM_PCIE_PENDING_OK,&lab_retained_pcie_pending[1],&result);
    }
    lab_broadcom_d3_disarm();
    serial_puts("LEANOS-LAB/1 BROADCOM-D3 profile=qotom-broadcom-d3-v1 index=14 status=");
    serial_u64(status);serial_puts(" command-attempted=");serial_u64(result.command_attempted);
    serial_puts(" command-before=");serial_u64(result.before_command);
    serial_puts(" command-after=");serial_u64(result.after_command);
    serial_puts(" polls=");serial_u64(result.pending_polls);
    serial_puts(" device-status=");serial_u64(result.device_status);
    serial_puts(" pmcsr-before=");serial_u64(result.before_pmcsr);
    serial_puts(" d3-attempted=");serial_u64(result.d3_attempted);
    serial_puts(" pmcsr-after=");serial_u64(result.after_pmcsr);serial_putc('\n');
    if(status!=QOTOM_BROADCOM_D3_OK)pre_admission_fail("qotom-broadcom-d3");
}
