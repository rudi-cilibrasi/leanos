#include "qotom-ecam-arm.h"
#include "qotom-pm-delay.h"
#include "qotom-pcie-pending.h"

static int lab_pcie_pending_timer_read(void *opaque,uint16_t port,uint32_t *value) {
    (void)opaque;
    if(port!=0x408 || !value)return 0;
    *value=in32(0x408);return 1;
}
static struct lab_pm_delay lab_pcie_pending_timer={.read32=lab_pcie_pending_timer_read};
static void lab_pcie_pending_disarm(void) {
    lab_ecam_window.armed=0;lab_pcie_pending_timer.armed=0;
}
static uint32_t lab_pcie_pending_arm(const struct lab_ecam_root_view *view) {
    lab_pcie_pending_disarm();
    if(!lab_ecam_arm(&lab_ecam_window,view,lab_ecam_tables,lab_ecam_table_count,
            (uintptr_t)lab_ecam_aperture))return 8;
    lab_ecam_window.armed=1;
    if(!lab_pm_delay_arm(&lab_pcie_pending_timer,lab_ecam_tables,
            lab_ecam_table_count,qotom_ecam_read,&lab_ecam_reader)) {
        lab_pcie_pending_disarm();return 9;
    }
    return 0;
}
static void lab_pcie_pending_emit(unsigned index,uint32_t status,
        const struct qotom_pcie_pending_result *result) {
    serial_puts("LEANOS-LAB/1 PCIE-PENDING profile=qotom-pcie-pending-v1 index=");serial_u64(index);
    serial_puts(" status=");serial_u64(status);
    serial_puts(" polls=");serial_u64(result->polls);
    serial_puts(" device-status=");serial_u64(result->device_status);serial_putc('\n');
}
static __attribute__((noinline)) void lab_capture_pcie_pending(
        const struct lab_ecam_root_view *view,const struct pci_enumeration_snapshot *snapshot) {
    if(snapshot->count!=16)pre_admission_fail("qotom-pcie-pending");
    for(unsigned fn=0;fn<4;++fn) {
        struct qotom_pcie_pending_result result={0};
        uint32_t status=8;
        if(qotom_rootport_pending_prior_valid(&snapshot->headers[6+fn],
                &lab_retained_pcie_device[6+fn],QOTOM_ROOTPORT_OK,
                &lab_retained_rootport_bme[fn])) {
            status=lab_pcie_pending_arm(view);
            if(!status)status=qotom_confirm_rootport_nonposted_quiet(
                qotom_ecam_read,&lab_ecam_reader,lab_pm_delay_wait,&lab_pcie_pending_timer,
                &snapshot->headers[6+fn],&lab_retained_pci_caps[6+fn],
                &lab_retained_pcie_device[6+fn],QOTOM_ROOTPORT_OK,
                &lab_retained_rootport_bme[fn],&result);
        }
        lab_pcie_pending_disarm();lab_pcie_pending_emit(6+fn,status,&result);
        if(status!=QOTOM_PCIE_PENDING_OK)pre_admission_fail("qotom-pcie-pending");
    }
    for(unsigned port=0;port<2;++port) {
        const unsigned index=13+2*port;
        struct qotom_pcie_pending_result result={0};
        uint32_t status=8;
        if(qotom_realtek_pending_prior_valid(&snapshot->headers[index],
                &lab_retained_pcie_device[index],QOTOM_REALTEK_OK,
                &lab_retained_realtek_state[port],QOTOM_REALTEK_BME_OK,
                &lab_retained_realtek_bme[port])) {
            status=lab_pcie_pending_arm(view);
            if(!status)status=qotom_confirm_realtek_nonposted_quiet(
                qotom_ecam_read,&lab_ecam_reader,lab_pm_delay_wait,&lab_pcie_pending_timer,
                &snapshot->headers[index],&lab_retained_pci_caps[index],
                &lab_retained_pcie_device[index],QOTOM_REALTEK_OK,
                &lab_retained_realtek_state[port],QOTOM_REALTEK_BME_OK,
                &lab_retained_realtek_bme[port],&result);
        }
        lab_pcie_pending_disarm();lab_pcie_pending_emit(index,status,&result);
        if(status!=QOTOM_PCIE_PENDING_OK)pre_admission_fail("qotom-pcie-pending");
    }
}
