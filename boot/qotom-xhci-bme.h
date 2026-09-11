#ifndef LEANOS_QOTOM_XHCI_BME_H
#define LEANOS_QOTOM_XHCI_BME_H
#include "qotom-xhci-operational.h"
typedef int (*qotom_xhci_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_xhci_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_xhci_bme_status {
    QOTOM_XHCI_BME_OK,QOTOM_XHCI_BME_ARGUMENT,QOTOM_XHCI_BME_PRIOR,
    QOTOM_XHCI_BME_REFRESH,QOTOM_XHCI_BME_STATE,QOTOM_XHCI_BME_COMMAND,
    QOTOM_XHCI_BME_WRITE,QOTOM_XHCI_BME_READBACK,QOTOM_XHCI_BME_FINAL
};
/* Exact captured stopped state, not a general controller-quiescence predicate. */
static inline int qotom_xhci_stopped_sample(const struct qotom_xhci_operational *s) {
    return s && !s->command && s->status_before==1 && s->status_after==1;
}
/* <=357 reads (two <=177-read collectors, three command reads), one word write.
 * Require immutable nonaliasing prior views and bounded serialized callbacks.
 * Clear only BME in the exact observed PCI Command 0006 -> 0002; do not write
 * the adjacent Status halfword, disable MMIO decoding, or restore BME on failure.
 * A failed write can have taken effect. Samples do not exclude continuing
 * firmware/AP access or prove posted-write drain/system DMA containment.
 * This helper does not grant native mapping/write authority or admit a platform. */
static inline enum qotom_xhci_bme_status qotom_clear_xhci_bme(
        pci_enumeration_read config,void *config_context,
        qotom_xhci_mmio_read capabilities,void *capabilities_context,
        qotom_xhci_mmio_read extended,void *extended_context,
        qotom_xhci_mmio_read operational,void *operational_context,
        qotom_xhci_write_word write,void *write_context,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,
        const struct qotom_xhci_legacy *legacy,
        enum qotom_xhci_smi_status smi_status,const struct qotom_xhci_smi_result *smi,
        enum qotom_xhci_operational_status prior_status,const struct qotom_xhci_operational *prior,
        struct qotom_xhci_bme_result *out) {
    if(out)*out=(struct qotom_xhci_bme_result){0};
    if(!config || !capabilities || !extended || !operational || !write || !header || !caps || !legacy || !smi || !prior || !out)
        return QOTOM_XHCI_BME_ARGUMENT;
    if(prior_status!=QOTOM_XHCI_OPERATIONAL_OK || !qotom_xhci_stopped_sample(prior) ||
       (header->words[1]&0xffff)!=0x6)return QOTOM_XHCI_BME_PRIOR;
    struct qotom_xhci_operational fresh={0};
    if(qotom_collect_xhci_operational(config,config_context,capabilities,capabilities_context,
            extended,extended_context,operational,operational_context,header,caps,legacy,smi_status,smi,&fresh)!=QOTOM_XHCI_OPERATIONAL_OK)
        return QOTOM_XHCI_BME_REFRESH;
    if(!qotom_xhci_stopped_sample(&fresh))return QOTOM_XHCI_BME_STATE;
    uint32_t command;
    if(!config(config_context,0,20,0,4,&command) || (command&0xffff)!=0x6)
        return QOTOM_XHCI_BME_COMMAND;
    out->before_command=command&0xffff;out->attempted=1;
    if(!write(write_context,0,20,0,4,0x2))return QOTOM_XHCI_BME_WRITE;
    if(!config(config_context,0,20,0,4,&command))return QOTOM_XHCI_BME_READBACK;
    out->after_command=command&0xffff;
    if(out->after_command!=0x2)return QOTOM_XHCI_BME_READBACK;
    struct qotom_xhci_operational final={0};
    if(qotom_collect_xhci_operational(config,config_context,capabilities,capabilities_context,
            extended,extended_context,operational,operational_context,header,caps,legacy,smi_status,smi,&final)!=QOTOM_XHCI_OPERATIONAL_OK ||
       !qotom_xhci_stopped_sample(&final))return QOTOM_XHCI_BME_FINAL;
    if(!config(config_context,0,20,0,4,&command))return QOTOM_XHCI_BME_FINAL;
    out->after_command=command&0xffff;
    if(out->after_command!=0x2)return QOTOM_XHCI_BME_FINAL;
    return QOTOM_XHCI_BME_OK;
}
#endif
