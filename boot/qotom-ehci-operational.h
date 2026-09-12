#ifndef LEANOS_QOTOM_EHCI_OPERATIONAL_H
#define LEANOS_QOTOM_EHCI_OPERATIONAL_H
#include "qotom-ehci-smi.h"

struct qotom_ehci_operational { uint32_t command,status,interrupt_enable,configured; };
enum qotom_ehci_operational_status {
    QOTOM_EHCI_OPERATIONAL_OK, QOTOM_EHCI_OPERATIONAL_ARGUMENT,
    QOTOM_EHCI_OPERATIONAL_PRIOR, QOTOM_EHCI_OPERATIONAL_REFRESH,
    QOTOM_EHCI_OPERATIONAL_STATE, QOTOM_EHCI_OPERATIONAL_READ,
    QOTOM_EHCI_OPERATIONAL_ABSENT, QOTOM_EHCI_OPERATIONAL_FINAL
};
/* Fixed captured CAPLENGTH, with offsets relative to the operational base.
 * EHCI 1.0 table 2-8 requires DWORD accesses. Address selection grants no
 * mapping authority; the native transaction must independently restrict it. */
static inline int qotom_ehci_operational_address(uint32_t capbase,uint32_t offset,uint64_t *out) {
    if(!out || capbase!=UINT32_C(0x01000020) ||
       (offset!=0 && offset!=4 && offset!=8 && offset!=0x40))return 0;
    *out=QOTOM_EHCI_BAR+(capbase&255)+offset;
    return 1;
}
/* At most 118 reads: two <=57-read binding refreshes bracket four sequential
 * operational samples. No writes, polling, reset or admission. A successful
 * result is not an atomic snapshot or evidence of continuing firmware exclusion
 * or drained DMA. Keep input/output views nonaliasing and immutable, serialize
 * trusted bounded callbacks, and establish fresh UC/no-alias/root authority.
 * Any failure publishes zero fields; raw reserved bits are retained on success
 * for review rather than interpreted as an operational compatibility claim. */
static inline enum qotom_ehci_operational_status qotom_collect_ehci_operational(
        pci_enumeration_read config,void *config_context,
        qotom_ehci_mmio_read capabilities,void *capabilities_context,
        qotom_ehci_mmio_read operational,void *operational_context,
        const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        enum qotom_ehci_smi_status prior_status,
        const struct qotom_ehci_smi_result *prior,
        struct qotom_ehci_operational *out) {
    if(out)*out=(struct qotom_ehci_operational){0};
    if(!config || !capabilities || !operational || !header || !caps || !prior || !out)
        return QOTOM_EHCI_OPERATIONAL_ARGUMENT;
    if(prior_status!=QOTOM_EHCI_SMI_OBSERVED || prior->write_attempted!=1 ||
       (prior->before_control&~(QOTOM_EHCI_SMI_ENABLE|QOTOM_EHCI_SMI_STATUS)) ||
       (prior->after_control&~QOTOM_EHCI_SMI_STATUS) ||
       caps->capbase!=UINT32_C(0x01000020) || caps->structural!=UINT32_C(0x00200008) ||
       caps->capability!=UINT32_C(0x00036881))return QOTOM_EHCI_OPERATIONAL_PRIOR;
    struct qotom_ehci_legacy_snapshot fresh={0};
    if(qotom_collect_ehci_legacy(config,config_context,capabilities,capabilities_context,header,caps,&fresh)!=QOTOM_EHCI_LEGACY_OK)
        return QOTOM_EHCI_OPERATIONAL_REFRESH;
    if(!qotom_ehci_smi_legacy_owned(&fresh) || (fresh.control_status&~QOTOM_EHCI_SMI_STATUS))
        return QOTOM_EHCI_OPERATIONAL_STATE;
    const uint32_t offsets[4]={0,4,8,0x40};
    uint32_t samples[4];
    for(unsigned i=0;i<4;++i) {
        uint64_t address;
        if(!qotom_ehci_operational_address(caps->capbase,offsets[i],&address))return QOTOM_EHCI_OPERATIONAL_PRIOR;
        if(!operational(operational_context,address,&samples[i]))return QOTOM_EHCI_OPERATIONAL_READ;
        if(samples[i]==UINT32_MAX)return QOTOM_EHCI_OPERATIONAL_ABSENT;
    }
    struct qotom_ehci_legacy_snapshot final={0};
    if(qotom_collect_ehci_legacy(config,config_context,capabilities,capabilities_context,header,caps,&final)!=QOTOM_EHCI_LEGACY_OK ||
       !qotom_ehci_smi_legacy_owned(&final) || (final.control_status&~QOTOM_EHCI_SMI_STATUS))
        return QOTOM_EHCI_OPERATIONAL_FINAL;
    *out=(struct qotom_ehci_operational){samples[0],samples[1],samples[2],samples[3]};
    return QOTOM_EHCI_OPERATIONAL_OK;
}
#endif
