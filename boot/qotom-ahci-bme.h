#ifndef LEANOS_QOTOM_AHCI_BME_H
#define LEANOS_QOTOM_AHCI_BME_H
#include "qotom-ahci-interrupts.h"
typedef int (*qotom_ahci_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_ahci_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_ahci_bme_status {
    QOTOM_AHCI_BME_OK,QOTOM_AHCI_BME_ARGUMENT,QOTOM_AHCI_BME_PRIOR,
    QOTOM_AHCI_BME_REFRESH,QOTOM_AHCI_BME_STATE,QOTOM_AHCI_BME_COMMAND,
    QOTOM_AHCI_BME_WRITE,QOTOM_AHCI_BME_READBACK,QOTOM_AHCI_BME_FINAL
};
/* <=77 reads: two complete 37-read collectors and three command reads.
 * One word write clears only BME, PCI Command 0007 -> 0003 at 00:13.0 +4.
 * Retain IO/MMIO decoding; never write adjacent PCI Status or restore BME.
 * Intel 329670-002 section 13.5.2 explicitly leaves split-transaction
 * completions unaffected by BME. This is not transaction-drain evidence.
 * Immutable nonaliasing observations, serialized bounded callbacks, native
 * firmware/root/resource binding and exclusion are caller obligations.
 * Failed writes can have effects; no retry/rollback or platform admission. */
static inline enum qotom_ahci_bme_status qotom_clear_ahci_bme(
        pci_enumeration_read config,void *config_context,
        qotom_ahci_mmio_read global,void *global_context,
        qotom_ahci_mmio_read port,void *port_context,
        qotom_ahci_write_word write,void *write_context,
        const struct pci_enumeration_header *header,
        enum qotom_ahci_status global_status,const struct qotom_ahci_capabilities *caps,
        enum qotom_ahci_port_status port_status,const struct qotom_ahci_port *prior,
        enum qotom_ahci_interrupt_status interrupt_status,
        const struct qotom_ahci_interrupt_result *interrupt,
        struct qotom_ahci_bme_result *out) {
    if(out)*out=(struct qotom_ahci_bme_result){0};
    if(!config || !global || !port || !write || !header || !caps || !prior || !interrupt || !out)
        return QOTOM_AHCI_BME_ARGUMENT;
    if(global_status!=QOTOM_AHCI_OK || port_status!=QOTOM_AHCI_PORT_OK ||
       interrupt_status!=QOTOM_AHCI_INTERRUPTS_OK || !qotom_ahci_port1_profile(caps) ||
       caps->control!=UINT32_C(0x80000002) || !qotom_ahci_port_stopped(prior) ||
       interrupt->write_attempted!=1 || interrupt->before_control!=caps->control ||
       interrupt->after_control!=UINT32_C(0x80000000) || (header->words[1]&0xffff)!=7)
        return QOTOM_AHCI_BME_PRIOR;
    struct qotom_ahci_capabilities disabled=*caps;disabled.control=interrupt->after_control;
    struct qotom_ahci_port fresh={0};
    if(qotom_collect_ahci_port(config,config_context,global,global_context,port,port_context,
            header,QOTOM_AHCI_OK,&disabled,&fresh)!=QOTOM_AHCI_PORT_OK)
        return QOTOM_AHCI_BME_REFRESH;
    if(!qotom_ahci_port_stopped(&fresh))return QOTOM_AHCI_BME_STATE;
    uint32_t command;
    if(!config(config_context,0,19,0,4,&command) || (command&0xffff)!=7)
        return QOTOM_AHCI_BME_COMMAND;
    out->before_command=command&0xffff;out->attempted=1;
    if(!write(write_context,0,19,0,4,3))return QOTOM_AHCI_BME_WRITE;
    if(!config(config_context,0,19,0,4,&command))return QOTOM_AHCI_BME_READBACK;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_AHCI_BME_READBACK;
    if(qotom_collect_ahci_port(config,config_context,global,global_context,port,port_context,
            header,QOTOM_AHCI_OK,&disabled,&fresh)!=QOTOM_AHCI_PORT_OK ||
       !qotom_ahci_port_stopped(&fresh))return QOTOM_AHCI_BME_FINAL;
    if(!config(config_context,0,19,0,4,&command))return QOTOM_AHCI_BME_FINAL;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_AHCI_BME_FINAL;
    return QOTOM_AHCI_BME_OK;
}
#endif
