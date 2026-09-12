#ifndef LEANOS_QOTOM_XHCI_OPERATIONAL_H
#define LEANOS_QOTOM_XHCI_OPERATIONAL_H
#include "qotom-xhci-smi.h"
struct qotom_xhci_operational { uint32_t status_before,command,status_after; };
enum qotom_xhci_operational_status {
    QOTOM_XHCI_OPERATIONAL_OK, QOTOM_XHCI_OPERATIONAL_ARGUMENT,
    QOTOM_XHCI_OPERATIONAL_PRIOR, QOTOM_XHCI_OPERATIONAL_REFRESH,
    QOTOM_XHCI_OPERATIONAL_STATE, QOTOM_XHCI_OPERATIONAL_READ,
    QOTOM_XHCI_OPERATIONAL_ABSENT, QOTOM_XHCI_OPERATIONAL_FINAL,
    QOTOM_XHCI_OPERATIONAL_NOT_READY
};
/* J1900 329670-002 sections14.7.9/14.7.10: fixed captured CAPLENGTH80,
 * USBCMD at80 and USBSTS at84. Address selection is not mapping authority. */
static inline int qotom_xhci_operational_address(uint32_t capbase,uint32_t offset,uint64_t *out) {
    if(!out || capbase!=UINT32_C(0x01000080) || (offset!=0 && offset!=4))return 0;
    *out=QOTOM_XHCI_BAR+0x80+offset;return 1;
}
/* <=177 reads: two complete <=87-read list/resource refreshes and three
 * operational samples. Read USBSTS before USBCMD and reject CNR at either
 * status sample. No writes, polling or reset. All failure output stays zero.
 * Successful sequential raw samples are not an atomic snapshot, halt/drain
 * proof, firmware exclusion or DMA authority. Caller supplies immutable,
 * nonaliasing views, serialized bounded callbacks and fresh mapping authority. */
static inline enum qotom_xhci_operational_status qotom_collect_xhci_operational(
        pci_enumeration_read config,void *config_context,
        qotom_xhci_mmio_read capabilities,void *capabilities_context,
        qotom_xhci_mmio_read extended,void *extended_context,
        qotom_xhci_mmio_read operational,void *operational_context,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,
        const struct qotom_xhci_legacy *previous,
        enum qotom_xhci_smi_status prior_status,
        const struct qotom_xhci_smi_result *prior,
        struct qotom_xhci_operational *out) {
    if(out)*out=(struct qotom_xhci_operational){0};
    if(!config || !capabilities || !extended || !operational || !header || !caps || !previous || !prior || !out)
        return QOTOM_XHCI_OPERATIONAL_ARGUMENT;
    if(prior_status!=QOTOM_XHCI_SMI_OBSERVED || prior->write_attempted!=1 ||
       (prior->before_control&~(QOTOM_XHCI_SMI_ENABLE|QOTOM_XHCI_SMI_STATUS)) ||
       (prior->after_control&~QOTOM_XHCI_SMI_STATUS) ||
       !previous->count || previous->count>QOTOM_XHCI_EXT_LIMIT || previous->legacy_offset!=0x8460 ||
       caps->words[0]!=UINT32_C(0x01000080))return QOTOM_XHCI_OPERATIONAL_PRIOR;
    struct qotom_xhci_legacy fresh={0};
    if(qotom_collect_xhci_legacy(config,config_context,capabilities,capabilities_context,
            extended,extended_context,header,caps,&fresh)!=QOTOM_XHCI_LEGACY_OK)
        return QOTOM_XHCI_OPERATIONAL_REFRESH;
    struct qotom_xhci_handoff_result difference={0};
    if(!qotom_xhci_smi_owned(&fresh) || (fresh.control_status&~QOTOM_XHCI_SMI_STATUS) ||
       qotom_xhci_final_difference(previous,&fresh,&difference))return QOTOM_XHCI_OPERATIONAL_STATE;
    const uint32_t offsets[3]={4,0,4};uint32_t samples[3];
    for(unsigned i=0;i<3;++i) {
        uint64_t address;
        if(!qotom_xhci_operational_address(caps->words[0],offsets[i],&address))return QOTOM_XHCI_OPERATIONAL_PRIOR;
        if(!operational(operational_context,address,&samples[i]))return QOTOM_XHCI_OPERATIONAL_READ;
        if(samples[i]==UINT32_MAX)return QOTOM_XHCI_OPERATIONAL_ABSENT;
        if(i!=1 && (samples[i]&0x800))return QOTOM_XHCI_OPERATIONAL_NOT_READY;
    }
    struct qotom_xhci_legacy final={0};
    if(qotom_collect_xhci_legacy(config,config_context,capabilities,capabilities_context,
            extended,extended_context,header,caps,&final)!=QOTOM_XHCI_LEGACY_OK ||
       !qotom_xhci_smi_owned(&final) || (final.control_status&~QOTOM_XHCI_SMI_STATUS) ||
       qotom_xhci_final_difference(&fresh,&final,&difference))return QOTOM_XHCI_OPERATIONAL_FINAL;
    *out=(struct qotom_xhci_operational){samples[0],samples[1],samples[2]};
    return QOTOM_XHCI_OPERATIONAL_OK;
}
#endif
