#ifndef LEANOS_QOTOM_XHCI_LEGACY_H
#define LEANOS_QOTOM_XHCI_LEGACY_H
#include "qotom-xhci-capabilities.h"
#define QOTOM_XHCI_EXT_LIMIT 48u
struct qotom_xhci_ext_header { uint32_t offset,raw; };
struct qotom_xhci_legacy {
    uint32_t count,legacy_offset,control_status;
    struct qotom_xhci_ext_header headers[QOTOM_XHCI_EXT_LIMIT];
};
enum qotom_xhci_legacy_status {
    QOTOM_XHCI_LEGACY_OK,QOTOM_XHCI_LEGACY_ARGUMENT,QOTOM_XHCI_LEGACY_REFRESH,
    QOTOM_XHCI_LEGACY_DRIFT,QOTOM_XHCI_LEGACY_POINTER,QOTOM_XHCI_LEGACY_LIMIT,
    QOTOM_XHCI_LEGACY_READ,QOTOM_XHCI_LEGACY_ID,QOTOM_XHCI_LEGACY_DUPLICATE,
    QOTOM_XHCI_LEGACY_OVERLAP,QOTOM_XHCI_LEGACY_FINAL
};
/* The captured chipset's extended capabilities occupy the resource's upper
 * half. This address gate is a closed observation envelope, not mapping authority. */
static inline int qotom_xhci_extended_address(uint32_t offset,uint64_t *out) {
    if(!out || offset<0x8000 || offset>0xfffc || (offset&3))return 0;
    *out=QOTOM_XHCI_BAR+offset;return 1;
}
static inline int qotom_xhci_caps_equal(const struct qotom_xhci_capabilities *a,
        const struct qotom_xhci_capabilities *b) {
    for(unsigned i=0;i<7;++i)if(a->words[i]!=b->words[i])return 0;
    return 1;
}
/* <=87 reads: two 19-read capability/binding refreshes, <=48 list headers and
 * one legacy control sample. xECP is BAR-relative DWORD units; subsequent NEXT
 * fields are forward displacements in DWORD units, unlike EHCI config pointers.
 * Immutable/nonaliasing views and bounded serialized trusted callbacks required.
 * No writes or operational access. Entire output remains zero on failure.
 * Refresh does not establish atomicity, ownership or continuing exclusion. */
static inline enum qotom_xhci_legacy_status qotom_collect_xhci_legacy(
        pci_enumeration_read config,void *config_context,
        qotom_xhci_mmio_read capabilities,void *capabilities_context,
        qotom_xhci_mmio_read extended,void *extended_context,
        const struct pci_enumeration_header *header,
        const struct qotom_xhci_capabilities *prior,struct qotom_xhci_legacy *out) {
    if(out)*out=(struct qotom_xhci_legacy){0};
    if(!config || !capabilities || !extended || !header || !prior || !out)
        return QOTOM_XHCI_LEGACY_ARGUMENT;
    struct qotom_xhci_capabilities fresh={0};
    if(qotom_collect_xhci_capabilities(config,config_context,capabilities,capabilities_context,
            header,&fresh)!=QOTOM_XHCI_OK)return QOTOM_XHCI_LEGACY_REFRESH;
    if(!qotom_xhci_caps_equal(prior,&fresh))return QOTOM_XHCI_LEGACY_DRIFT;
    uint32_t offset=(fresh.words[4]>>16)*4u;
    struct qotom_xhci_legacy result={0};
    while(offset) {
        uint64_t address;
        if(!qotom_xhci_extended_address(offset,&address))return QOTOM_XHCI_LEGACY_POINTER;
        if(result.count==QOTOM_XHCI_EXT_LIMIT)return QOTOM_XHCI_LEGACY_LIMIT;
        uint32_t raw;
        if(!extended(extended_context,address,&raw))return QOTOM_XHCI_LEGACY_READ;
        uint32_t id=raw&255;
        if(!id || id==255)return QOTOM_XHCI_LEGACY_ID;
        result.headers[result.count++]=(struct qotom_xhci_ext_header){offset,raw};
        if(id==1) {
            if(result.legacy_offset)return QOTOM_XHCI_LEGACY_DUPLICATE;
            if(offset>0xfff8)return QOTOM_XHCI_LEGACY_POINTER;
            result.legacy_offset=offset;
        }
        uint32_t next=(raw>>8)&255;
        if(next && id==1 && next==1)return QOTOM_XHCI_LEGACY_OVERLAP;
        offset=next?offset+next*4u:0;
    }
    if(result.legacy_offset) {
        uint64_t address;
        if(!qotom_xhci_extended_address(result.legacy_offset+4,&address))return QOTOM_XHCI_LEGACY_POINTER;
        if(!extended(extended_context,address,&result.control_status) || result.control_status==UINT32_MAX)
            return QOTOM_XHCI_LEGACY_READ;
    }
    if(qotom_collect_xhci_capabilities(config,config_context,capabilities,capabilities_context,
            header,&fresh)!=QOTOM_XHCI_OK || !qotom_xhci_caps_equal(prior,&fresh))
        return QOTOM_XHCI_LEGACY_FINAL;
    *out=result;return QOTOM_XHCI_LEGACY_OK;
}
#endif
