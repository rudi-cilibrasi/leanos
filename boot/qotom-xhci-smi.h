#ifndef LEANOS_QOTOM_XHCI_SMI_H
#define LEANOS_QOTOM_XHCI_SMI_H
#include "qotom-xhci-handoff.h"
#define QOTOM_XHCI_SMI_ENABLE UINT32_C(0x0000e011)
#define QOTOM_XHCI_SMI_STATUS UINT32_C(0xe0110000)
enum qotom_xhci_smi_status {
    QOTOM_XHCI_SMI_OBSERVED, QOTOM_XHCI_SMI_ARGUMENT,
    QOTOM_XHCI_SMI_PRIOR, QOTOM_XHCI_SMI_REFRESH,
    QOTOM_XHCI_SMI_STATE, QOTOM_XHCI_SMI_WRITE,
    QOTOM_XHCI_SMI_FINAL, QOTOM_XHCI_SMI_READBACK
};
struct qotom_xhci_smi_result { uint32_t write_attempted,before_control,after_control; };
static inline int qotom_xhci_smi_owned(const struct qotom_xhci_legacy *s) {
    if(s->count>QOTOM_XHCI_EXT_LIMIT || s->legacy_offset!=0x8460)return 0;
    for(uint32_t i=0;i<s->count;++i)
        if(s->headers[i].offset==s->legacy_offset)
            return s->headers[i].raw==UINT32_C(0x01000801);
    return 0;
}
/* J1900 329670-002 section 14.7.189, USBLEGCTLSTS at 8464:
 * RW enables 15:13,4,0; RO status20,16; W1C status31:29.
 * Zero clears enables without acknowledging W1C status. Other bits must be zero.
 * <=174 reads (two bounded complete collectors), one fixed zero DWORD write.
 * Caller supplies immutable nonaliasing successful observations, serialized
 * mappings, stable resources and bounded trusted callbacks. No native backend
 * is provided here. Failed writes may have effects; no rollback. Observations
 * do not prove firmware exclusion, controller halt, drain or DMA containment. */
static inline enum qotom_xhci_smi_status qotom_disable_xhci_smi(
        pci_enumeration_read config,void *config_context,
        qotom_xhci_mmio_read mmio,void *mmio_context,
        qotom_xhci_mmio_read extended,void *extended_context,
        qotom_xhci_write_dword write,void *write_context,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,
        const struct qotom_xhci_legacy *previous,
        enum qotom_xhci_handoff_status handoff_status,
        const struct qotom_xhci_handoff_result *handoff,
        struct qotom_xhci_smi_result *out) {
    if(out)*out=(struct qotom_xhci_smi_result){0};
    if(!config || !mmio || !extended || !write || !header || !caps || !previous || !handoff || !out)
        return QOTOM_XHCI_SMI_ARGUMENT;
    const uint32_t reserved=~(QOTOM_XHCI_SMI_ENABLE|QOTOM_XHCI_SMI_STATUS);
    if(handoff_status!=QOTOM_XHCI_HANDOFF_OBSERVED || handoff->write_attempted!=1 ||
       !handoff->polls || handoff->polls>QOTOM_XHCI_HANDOFF_POLLS ||
       handoff->last_support!=UINT32_C(0x01000801) || (handoff->final_control&reserved) ||
       handoff->verify_kind || handoff->verify_index || handoff->verify_expected || handoff->verify_observed ||
       !previous->count || previous->count>QOTOM_XHCI_EXT_LIMIT || previous->legacy_offset!=0x8460)
        return QOTOM_XHCI_SMI_PRIOR;
    struct qotom_xhci_legacy fresh={0};
    if(qotom_collect_xhci_legacy(config,config_context,mmio,mmio_context,extended,extended_context,header,caps,&fresh)!=QOTOM_XHCI_LEGACY_OK)
        return QOTOM_XHCI_SMI_REFRESH;
    struct qotom_xhci_handoff_result difference={0};
    if(!qotom_xhci_smi_owned(&fresh) || qotom_xhci_final_difference(previous,&fresh,&difference) ||
       (fresh.control_status&reserved) || ((fresh.control_status^handoff->final_control)&QOTOM_XHCI_SMI_ENABLE))
        return QOTOM_XHCI_SMI_STATE;
    out->before_control=fresh.control_status;
    out->write_attempted=1;
    if(!write(write_context,QOTOM_XHCI_BAR+UINT64_C(0x8464),0))return QOTOM_XHCI_SMI_WRITE;
    struct qotom_xhci_legacy final={0};
    if(qotom_collect_xhci_legacy(config,config_context,mmio,mmio_context,extended,extended_context,header,caps,&final)!=QOTOM_XHCI_LEGACY_OK ||
       !qotom_xhci_smi_owned(&final) || qotom_xhci_final_difference(&fresh,&final,&difference))return QOTOM_XHCI_SMI_FINAL;
    out->after_control=final.control_status;
    if(final.control_status&~QOTOM_XHCI_SMI_STATUS)return QOTOM_XHCI_SMI_READBACK;
    return QOTOM_XHCI_SMI_OBSERVED;
}
#endif
