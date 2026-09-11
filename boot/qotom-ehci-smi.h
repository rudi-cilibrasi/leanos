#ifndef LEANOS_QOTOM_EHCI_SMI_H
#define LEANOS_QOTOM_EHCI_SMI_H
#include "qotom-ehci-handoff.h"
#define QOTOM_EHCI_SMI_ENABLE UINT32_C(0x0000e03f)
#define QOTOM_EHCI_SMI_STATUS UINT32_C(0xe03f0000)
typedef int (*qotom_ehci_write_dword)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint32_t);
enum qotom_ehci_smi_status {
    QOTOM_EHCI_SMI_OBSERVED, QOTOM_EHCI_SMI_ARGUMENT,
    QOTOM_EHCI_SMI_PRIOR, QOTOM_EHCI_SMI_REFRESH,
    QOTOM_EHCI_SMI_STATE, QOTOM_EHCI_SMI_WRITE,
    QOTOM_EHCI_SMI_FINAL, QOTOM_EHCI_SMI_READBACK
};
struct qotom_ehci_smi_result { uint32_t write_attempted,before_control,after_control; };
static inline int qotom_ehci_smi_legacy_owned(const struct qotom_ehci_legacy_snapshot *s) {
    return s->count==1 && s->legacy_offset==0x68 && s->headers[0].offset==0x68 &&
           s->headers[0].raw==UINT32_C(0x01000001);
}
/* EHCI 1.0 section 2.1.8: enable bits 15:13,5:0; RO status 21:16;
 * W1C status 31:29; all other bits reserved zero. A zero dword clears enables,
 * does not acknowledge W1C bits, and writes zero to reserved positions.
 * <=114 reads (two bounded collectors) and one dword write at fixed 00:1d.0+6c.
 * Caller supplies the successful handoff result, immutable nonaliasing views,
 * serialized mappings and bounded trusted callbacks. A failed write may have
 * taken effect; no rollback. Results are observations, not firmware exclusion,
 * controller halt, drained transactions or platform/DMA admission. */
static inline enum qotom_ehci_smi_status qotom_disable_ehci_smi(
        pci_enumeration_read config,void *config_context,
        qotom_ehci_mmio_read mmio,void *mmio_context,
        qotom_ehci_write_dword write,void *write_context,
        const struct pci_enumeration_header *header,
        const struct qotom_ehci_capabilities *caps,
        enum qotom_ehci_handoff_status handoff_status,
        const struct qotom_ehci_handoff_result *handoff,
        struct qotom_ehci_smi_result *out) {
    if(out)*out=(struct qotom_ehci_smi_result){0};
    if(!config || !mmio || !write || !header || !caps || !handoff || !out)return QOTOM_EHCI_SMI_ARGUMENT;
    const uint32_t reserved=~(QOTOM_EHCI_SMI_ENABLE|QOTOM_EHCI_SMI_STATUS);
    if(handoff_status!=QOTOM_EHCI_HANDOFF_OBSERVED || handoff->write_attempted!=1 ||
       !handoff->polls || handoff->polls>QOTOM_EHCI_HANDOFF_POLLS ||
       handoff->last_support!=UINT32_C(0x01000001) || (handoff->final_control&reserved))
        return QOTOM_EHCI_SMI_PRIOR;
    struct qotom_ehci_legacy_snapshot fresh={0};
    if(qotom_collect_ehci_legacy(config,config_context,mmio,mmio_context,header,caps,&fresh)!=QOTOM_EHCI_LEGACY_OK)
        return QOTOM_EHCI_SMI_REFRESH;
    if(!qotom_ehci_smi_legacy_owned(&fresh) || (fresh.control_status&reserved) ||
       ((fresh.control_status^handoff->final_control)&QOTOM_EHCI_SMI_ENABLE))
        return QOTOM_EHCI_SMI_STATE;
    out->before_control=fresh.control_status;
    out->write_attempted=1;
    if(!write(write_context,0,29,0,0x6c,0))return QOTOM_EHCI_SMI_WRITE;
    struct qotom_ehci_legacy_snapshot final={0};
    if(qotom_collect_ehci_legacy(config,config_context,mmio,mmio_context,header,caps,&final)!=QOTOM_EHCI_LEGACY_OK ||
       !qotom_ehci_smi_legacy_owned(&final))return QOTOM_EHCI_SMI_FINAL;
    out->after_control=final.control_status;
    if(final.control_status&~QOTOM_EHCI_SMI_STATUS)return QOTOM_EHCI_SMI_READBACK;
    return QOTOM_EHCI_SMI_OBSERVED;
}
#endif
