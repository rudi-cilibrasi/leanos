#ifndef LEANOS_QOTOM_XHCI_CAPABILITIES_H
#define LEANOS_QOTOM_XHCI_CAPABILITIES_H
#include "pci-enumeration.h"
#define QOTOM_XHCI_BAR UINT64_C(0xd0900000)
typedef int (*qotom_xhci_mmio_read)(void *,uint64_t,uint32_t *);
struct qotom_xhci_capabilities { uint32_t words[7]; };
enum qotom_xhci_status {
    QOTOM_XHCI_OK,QOTOM_XHCI_ARGUMENT,QOTOM_XHCI_HEADER,
    QOTOM_XHCI_CONFIG_READ,QOTOM_XHCI_DRIFT,QOTOM_XHCI_MMIO_READ,
    QOTOM_XHCI_ABSENT,QOTOM_XHCI_FORMAT
};
/* Selection only. Caller independently establishes UC mapping, alias exclusion,
 * root binding and serialized bounded trusted callbacks before any access. */
static inline int qotom_xhci_capability_address(uint32_t offset,uint64_t *out) {
    if(!out || offset>0x18 || (offset&3))return 0;
    *out=QOTOM_XHCI_BAR+offset;return 1;
}
/* Captured 00:14.0 has a 64-bit, non-prefetchable BAR at 10h/14h. Six config
 * reads bracket seven capability samples (<=19 reads). No writes or operational
 * access. Input/output must not alias; input views remain immutable. Refresh is
 * not atomicity or firmware exclusion. All failure output is zero. */
static inline enum qotom_xhci_status qotom_collect_xhci_capabilities(
        pci_enumeration_read config,void *config_context,
        qotom_xhci_mmio_read mmio,void *mmio_context,
        const struct pci_enumeration_header *header,
        struct qotom_xhci_capabilities *out) {
    if(out)*out=(struct qotom_xhci_capabilities){0};
    if(!config || !mmio || !header || !out)return QOTOM_XHCI_ARGUMENT;
    if(header->bus || header->device!=20 || header->function ||
       header->words[0]!=UINT32_C(0x0f358086) || header->words[2]!=UINT32_C(0x0c03300e) ||
       (header->words[3]&UINT32_C(0x00ff0000)) || !(header->words[1]&2) ||
       header->words[4]!=UINT32_C(0xd0900004) || header->words[5])return QOTOM_XHCI_HEADER;
    const uint32_t masks[6]={UINT32_MAX,2,UINT32_MAX,UINT32_C(0x00ff0000),UINT32_MAX,UINT32_MAX};
    struct qotom_xhci_capabilities sampled={0};
    for(unsigned pass=0;pass<2;++pass) {
        for(unsigned i=0;i<6;++i) {
            uint32_t raw;
            if(!config(config_context,0,20,0,(uint8_t)(i*4),&raw))return QOTOM_XHCI_CONFIG_READ;
            if((raw&masks[i])!=(header->words[i]&masks[i]))return QOTOM_XHCI_DRIFT;
        }
        if(pass)break;
        for(unsigned i=0;i<7;++i) {
            uint64_t address;
            if(!qotom_xhci_capability_address(i*4,&address))return QOTOM_XHCI_ARGUMENT;
            if(!mmio(mmio_context,address,&sampled.words[i]))return QOTOM_XHCI_MMIO_READ;
            if(sampled.words[i]==UINT32_MAX)return QOTOM_XHCI_ABSENT;
        }
        /* Closed xHCI 1.0 candidate: captured chipset specifies CAPLENGTH80h.
         * Preserve parameter/offset words raw; do not follow any pointer here. */
        if(sampled.words[0]!=UINT32_C(0x01000080))return QOTOM_XHCI_FORMAT;
    }
    *out=sampled;return QOTOM_XHCI_OK;
}
#endif
