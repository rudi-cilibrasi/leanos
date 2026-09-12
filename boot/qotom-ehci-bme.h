#ifndef LEANOS_QOTOM_EHCI_BME_H
#define LEANOS_QOTOM_EHCI_BME_H
#include "qotom-ehci-operational.h"
typedef int (*qotom_ehci_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_ehci_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_ehci_bme_status {
    QOTOM_EHCI_BME_OK,QOTOM_EHCI_BME_ARGUMENT,QOTOM_EHCI_BME_PRIOR,
    QOTOM_EHCI_BME_REFRESH,QOTOM_EHCI_BME_STATE,QOTOM_EHCI_BME_COMMAND,
    QOTOM_EHCI_BME_WRITE,QOTOM_EHCI_BME_READBACK,QOTOM_EHCI_BME_FINAL
};
/* Exact captured stopped state, not a general controller-quiescence predicate. */
static inline int qotom_ehci_stopped_sample(const struct qotom_ehci_operational *s) {
    return s && s->command==UINT32_C(0x80000) && s->status==0x1000 &&
        !s->interrupt_enable && !s->configured;
}
/* <=239 reads (two <=118-read collectors, three command reads), one word write.
 * Require immutable nonaliasing prior views and bounded serialized callbacks.
 * Clear only BME in the exact observed PCI Command 0406 -> 0402; do not write
 * the adjacent Status halfword, disable MMIO decoding, or restore BME on failure.
 * A failed write can have taken effect. Samples do not exclude continuing
 * firmware/AP access or prove posted-write drain/system DMA containment.
 * This helper does not grant native mapping/write authority or admit a platform. */
static inline enum qotom_ehci_bme_status qotom_clear_ehci_bme(
        pci_enumeration_read config,void *config_context,
        qotom_ehci_mmio_read capabilities,void *capabilities_context,
        qotom_ehci_mmio_read operational,void *operational_context,
        qotom_ehci_write_word write,void *write_context,
        const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        enum qotom_ehci_smi_status smi_status,const struct qotom_ehci_smi_result *smi,
        enum qotom_ehci_operational_status prior_status,const struct qotom_ehci_operational *prior,
        struct qotom_ehci_bme_result *out) {
    if(out)*out=(struct qotom_ehci_bme_result){0};
    if(!config || !capabilities || !operational || !write || !header || !caps || !smi || !prior || !out)
        return QOTOM_EHCI_BME_ARGUMENT;
    if(prior_status!=QOTOM_EHCI_OPERATIONAL_OK || !qotom_ehci_stopped_sample(prior) ||
       (header->words[1]&0xffff)!=0x406)return QOTOM_EHCI_BME_PRIOR;
    struct qotom_ehci_operational fresh={0};
    if(qotom_collect_ehci_operational(config,config_context,capabilities,capabilities_context,
            operational,operational_context,header,caps,smi_status,smi,&fresh)!=QOTOM_EHCI_OPERATIONAL_OK)
        return QOTOM_EHCI_BME_REFRESH;
    if(!qotom_ehci_stopped_sample(&fresh))return QOTOM_EHCI_BME_STATE;
    uint32_t command;
    if(!config(config_context,0,29,0,4,&command) || (command&0xffff)!=0x406)
        return QOTOM_EHCI_BME_COMMAND;
    out->before_command=command&0xffff;out->attempted=1;
    if(!write(write_context,0,29,0,4,0x402))return QOTOM_EHCI_BME_WRITE;
    if(!config(config_context,0,29,0,4,&command))return QOTOM_EHCI_BME_READBACK;
    out->after_command=command&0xffff;
    if(out->after_command!=0x402)return QOTOM_EHCI_BME_READBACK;
    struct qotom_ehci_operational final={0};
    if(qotom_collect_ehci_operational(config,config_context,capabilities,capabilities_context,
            operational,operational_context,header,caps,smi_status,smi,&final)!=QOTOM_EHCI_OPERATIONAL_OK ||
       !qotom_ehci_stopped_sample(&final))return QOTOM_EHCI_BME_FINAL;
    if(!config(config_context,0,29,0,4,&command))return QOTOM_EHCI_BME_FINAL;
    out->after_command=command&0xffff;
    if(out->after_command!=0x402)return QOTOM_EHCI_BME_FINAL;
    return QOTOM_EHCI_BME_OK;
}
#endif
