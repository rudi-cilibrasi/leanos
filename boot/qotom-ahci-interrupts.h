#ifndef LEANOS_QOTOM_AHCI_INTERRUPTS_H
#define LEANOS_QOTOM_AHCI_INTERRUPTS_H
#include "qotom-ahci-port.h"

typedef int (*qotom_ahci_write_dword)(void *,uint64_t,uint32_t);
enum qotom_ahci_interrupt_status {
    QOTOM_AHCI_INTERRUPTS_OK, QOTOM_AHCI_INTERRUPTS_ARGUMENT,
    QOTOM_AHCI_INTERRUPTS_PRIOR, QOTOM_AHCI_INTERRUPTS_REFRESH,
    QOTOM_AHCI_INTERRUPTS_STATE, QOTOM_AHCI_INTERRUPTS_WRITE,
    QOTOM_AHCI_INTERRUPTS_READ, QOTOM_AHCI_INTERRUPTS_READBACK,
    QOTOM_AHCI_INTERRUPTS_FINAL
};
struct qotom_ahci_interrupt_result { uint32_t write_attempted,before_control,after_control; };
/* Captured single-port stopped/empty profile, not a transaction-drain proof. */
static inline int qotom_ahci_port_stopped(const struct qotom_ahci_port *p) {
    return p && p->command_before==6 && p->interrupt_enable==0 &&
        p->task_file==0x50 && p->sata_status==0x123 && p->active==0 &&
        p->issued==0 && p->command_after==6;
}
/* Intel 329670-002 section 13.8.2: GHC bit31 AE, bit1 IE, bit0 HR.
 * One DWORD 80000000 at ABAR+4 clears IE while retaining AE and writing HR=0.
 * Two complete 37-read port/global/resource refreshes plus immediate GHC
 * readback: <=75 reads, one write, no reset, port write, polling or BME change.
 * Prior success is mandatory; resource/root/firmware binding, immutable
 * nonaliasing observations and serialized bounded callbacks are caller duties.
 * Failed writes may have effects. Retain attempted/before/after evidence;
 * no retry or rollback. This does not establish firmware exclusion or DMA drain. */
static inline enum qotom_ahci_interrupt_status qotom_disable_ahci_interrupts(
        pci_enumeration_read config,void *config_context,
        qotom_ahci_mmio_read global,void *global_context,
        qotom_ahci_mmio_read port,void *port_context,
        qotom_ahci_write_dword write,void *write_context,
        const struct pci_enumeration_header *header,
        enum qotom_ahci_status global_status,const struct qotom_ahci_capabilities *caps,
        enum qotom_ahci_port_status port_status,const struct qotom_ahci_port *prior,
        struct qotom_ahci_interrupt_result *out) {
    if(out)*out=(struct qotom_ahci_interrupt_result){0};
    if(!config || !global || !port || !write || !header || !caps || !prior || !out)
        return QOTOM_AHCI_INTERRUPTS_ARGUMENT;
    if(global_status!=QOTOM_AHCI_OK || port_status!=QOTOM_AHCI_PORT_OK ||
       !qotom_ahci_port1_profile(caps) || caps->control!=UINT32_C(0x80000002) ||
       !qotom_ahci_port_stopped(prior))return QOTOM_AHCI_INTERRUPTS_PRIOR;
    struct qotom_ahci_port fresh={0};
    if(qotom_collect_ahci_port(config,config_context,global,global_context,port,port_context,
            header,global_status,caps,&fresh)!=QOTOM_AHCI_PORT_OK)
        return QOTOM_AHCI_INTERRUPTS_REFRESH;
    if(!qotom_ahci_port_stopped(&fresh))return QOTOM_AHCI_INTERRUPTS_STATE;
    out->before_control=caps->control;out->write_attempted=1;
    if(!write(write_context,QOTOM_AHCI_BAR+4,UINT32_C(0x80000000)))
        return QOTOM_AHCI_INTERRUPTS_WRITE;
    uint32_t control=0;
    if(!global(global_context,QOTOM_AHCI_BAR+4,&control))return QOTOM_AHCI_INTERRUPTS_READ;
    out->after_control=control;
    if(control!=UINT32_C(0x80000000))return QOTOM_AHCI_INTERRUPTS_READBACK;
    struct qotom_ahci_capabilities disabled=*caps;disabled.control=control;
    if(qotom_collect_ahci_port(config,config_context,global,global_context,port,port_context,
            header,QOTOM_AHCI_OK,&disabled,&fresh)!=QOTOM_AHCI_PORT_OK ||
       !qotom_ahci_port_stopped(&fresh))return QOTOM_AHCI_INTERRUPTS_FINAL;
    return QOTOM_AHCI_INTERRUPTS_OK;
}
#endif
