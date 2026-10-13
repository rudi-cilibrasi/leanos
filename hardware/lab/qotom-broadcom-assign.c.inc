/* Reviewed Broadcom assignment (issue #559, docs/qotom-broadcom-assignment.md):
 * the qotom-j1900-pci-trust-v1-bcm43224-assign-v1 variant of the audited
 * PCI trust contract. It replaces the lab-only D3hot -> D0 step of the
 * network-subject image (issue #450).
 *
 * Inputs retained earlier in this boot: the native inventory header,
 * capability list and PCIe observation of 02:00.0, the exact D3hot record and
 * the final Command vector the trust contract accepted. The generated
 * contract result for that vector, the D3 record, the program's declared
 * policy and every configuration observation go to the two generated checks
 * of LeanOS/QotomBroadcomAssignment.lean.
 *
 * Configuration access uses mechanism 1 (CF8/CFC), as the bound program's
 * own configuration hooks do, and only for 02:00.0. The single store is the
 * 16-bit PMCSR word at offset 44 through the one-grant window. The D3hot ->
 * D0 recovery and the quiet-sample spacing use the ACPI PM timer delay of
 * the device-program hooks. */
#include "qotom-broadcom-assign-arm.h"

static int lab_broadcom_assign_read(void *opaque,uint8_t bus,uint8_t device,
        uint8_t function,uint8_t offset,uint32_t *value) {
    (void)opaque;
    if(bus!=2 || device || function || (offset&3) || !value)return 0;
    out32(0xcf8,UINT32_C(0x80020000)|offset);
    *value=in32(0xcfc);return 1;
}
static int lab_broadcom_assign_store16(void *opaque,uint8_t bus,uint8_t device,
        uint8_t function,uint8_t offset,uint16_t value) {
    (void)opaque;
    if(bus!=2 || device || function || offset!=QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET)return 0;
    out32(0xcf8,UINT32_C(0x80020000)|offset);
    out16(0xcfc,value);return 1;
}
static int lab_broadcom_assign_wait(void *opaque,uint32_t milliseconds) {
    (void)opaque;
    if(milliseconds!=QOTOM_BROADCOM_ASSIGN_RECOVERY_MS)return 0;
    wifi_hook_delay_us(milliseconds*1000u);return 1;
}
static struct lab_broadcom_assign_window lab_broadcom_assign_writer={
    .store16=lab_broadcom_assign_store16
};

/* Native status 11: the contract, priors or policy did not arm the window. */
static __attribute__((noinline)) void lab_broadcom_assign(const struct wifi_target *target,
        const struct wifi_policy *declared) {
    const struct qotom_broadcom_assign_policy policy={target->bus,target->dev,
        target->fn,target->id,declared->dma,declared->cfg_write,declared->cmd_set};
    const uint16_t *c=lab_retained_pci_final_commands;
    uint64_t contract=lab_retained_pci_final_match ?
        leanos_qotom_pci_initial_trust_contract(c[0],c[1],c[2],c[3],c[4],c[5],c[6],
            c[7],c[8],c[9],c[10],c[11],c[12],c[13],c[14],c[15]) : 0;
    enum qotom_broadcom_d3_status d3_status=
        (enum qotom_broadcom_d3_status)lab_retained_broadcom_d3_status;
    struct qotom_broadcom_assign_result result={0};
    uint32_t status=11;
    lab_broadcom_assign_writer.armed=0;
    if(lab_broadcom_assign_arm(&lab_broadcom_assign_writer,contract,d3_status,
            &lab_retained_broadcom_d3,&lab_retained_broadcom_endpoint,
            &lab_retained_pci_caps[14],&lab_retained_pcie_device[14],&policy))
        status=qotom_broadcom_assign_d0(lab_broadcom_assign_read,0,
            lab_broadcom_assign_window_write,&lab_broadcom_assign_writer,
            lab_broadcom_assign_wait,0,&lab_retained_broadcom_endpoint,
            &lab_retained_pci_caps[14],&lab_retained_pcie_device[14],
            d3_status,&lab_retained_broadcom_d3,contract,&policy,
            leanos_qotom_broadcom_assign_write,leanos_qotom_broadcom_assign_admission,
            &result);
    lab_broadcom_assign_writer.armed=0;
    serial_puts("LEANOS-LAB/1 BROADCOM-ASSIGN profile=qotom-j1900-pci-trust-v1-bcm43224-assign-v1 device=2:0.0 status=");
    serial_u64(status);serial_puts(" contract=");serial_u64(contract);
    serial_puts(" pmcsr-before=");serial_u64(result.pre_pmcsr);
    serial_puts(" command-before=");serial_u64(result.pre_command);
    serial_puts(" d0-attempted=");serial_u64(result.d0_attempted);
    serial_puts(" pmcsr-after=");serial_u64(result.after_pmcsr);
    serial_puts(" command-after=");serial_u64(result.post_command);
    serial_puts(" bar0=");serial_u64(result.post_bar0);
    serial_puts(" bar1=");serial_u64(result.post_bar1);
    serial_puts(" polls=");serial_u64(result.pending_polls);
    serial_puts(" device-status=");serial_u64(result.device_status);
    serial_puts(" admitted=");serial_u64(result.admitted);serial_putc('\n');
    if(status!=QOTOM_BROADCOM_ASSIGN_OK || result.admitted!=1)
        pre_admission_fail("qotom-broadcom-assign");
}
