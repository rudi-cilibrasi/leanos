#ifndef LEANOS_LAB_QOTOM_XHCI_BME_ARM_H
#define LEANOS_LAB_QOTOM_XHCI_BME_ARM_H
#include "qotom-ecam-firmware.h"
#include "qotom-ecam-root.h"
#include "qotom-xhci-bme-window.h"
#include "qotom-xhci-bme.h"

/* Closed lab binding for the word-sized BME clear request. This consumes immutable
 * successful collector samples, not arbitrary hardware claims. The caller
 * refreshes the binding through qotom_clear_xhci_bme before the write.
 * Root/firmware views and callbacks are trusted and stable for the transaction.
 * Rejection revokes prior authority; arming performs no device access. */
static inline int lab_xhci_bme_arm(struct lab_xhci_bme_window *w,
        const struct lab_ecam_root_view *view,
        const struct lab_ecam_firmware_table *tables,uint32_t count,
        uint64_t address,const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *caps,
        enum qotom_xhci_smi_status smi_status,const struct qotom_xhci_smi_result *smi,
        enum qotom_xhci_operational_status status,const struct qotom_xhci_operational *prior) {
    if(!w)return 0;
    w->armed=0;w->leaf=0;w->root=0;w->window=0;
    if(!header || header->bus || header->device!=20 || header->function ||
       header->words[0]!=UINT32_C(0x0f358086) || header->words[2]!=UINT32_C(0x0c03300e) ||
       (header->words[3]&UINT32_C(0x00ff0000)) || (header->words[1]&0xffff)!=0x6 ||
       header->words[4]!=(QOTOM_XHCI_BAR|4) || header->words[5] || !caps || !smi ||
       smi_status!=QOTOM_XHCI_SMI_OBSERVED || smi->write_attempted!=1 ||
       smi->before_control!=0x2000 || smi->after_control!=0 ||
       status!=QOTOM_XHCI_OPERATIONAL_OK || !qotom_xhci_stopped_sample(prior))return 0;
    static const uint32_t expected[7]={0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000};
    for(unsigned i=0;i<7;++i)if(caps->words[i]!=expected[i])return 0;
    if(!view || !w->controls || !w->invalidate || !w->store16 || !w->fault ||
       !lab_ecam_firmware_matches(tables,count))return 0;
    struct lab_ecam_controls before,after;
    if(!w->controls(w->opaque,&before) || !lab_ecam_controls_match(&before,view->root_address) ||
       !lab_ecam_root_matches(view,before.cr3,address))return 0;
    /* root_matches excludes all ECAM aliases. Also keep the entire XHCI MMIO resource
     * unaliased while its capability refresh shares this private aperture. */
    for(unsigned i=0;i<4096;++i)
        if((view->pt[i]&1) && (view->pt[i]&UINT64_C(0x000fffffffff0000))==QOTOM_XHCI_BAR)return 0;
    if(!w->controls(w->opaque,&after) || !lab_ecam_controls_match(&after,view->root_address))return 0;
    w->leaf=&view->pt[address/4096u];w->root=view->root_address;w->window=address;w->armed=1;
    return 1;
}
#endif
