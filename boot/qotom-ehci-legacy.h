#ifndef LEANOS_QOTOM_EHCI_LEGACY_H
#define LEANOS_QOTOM_EHCI_LEGACY_H
#include "qotom-ehci-capabilities.h"
#define QOTOM_EHCI_EXT_CAPACITY 48u
struct qotom_ehci_extended_header { uint8_t offset; uint32_t raw; };
struct qotom_ehci_legacy_snapshot {
    uint32_t count;
    uint8_t legacy_offset;
    uint32_t control_status;
    struct qotom_ehci_extended_header headers[QOTOM_EHCI_EXT_CAPACITY];
};
enum qotom_ehci_legacy_status {
    QOTOM_EHCI_LEGACY_OK, QOTOM_EHCI_LEGACY_ARGUMENT,
    QOTOM_EHCI_LEGACY_REFRESH, QOTOM_EHCI_LEGACY_DRIFT,
    QOTOM_EHCI_LEGACY_POINTER, QOTOM_EHCI_LEGACY_CYCLE,
    QOTOM_EHCI_LEGACY_READ, QOTOM_EHCI_LEGACY_ID,
    QOTOM_EHCI_LEGACY_DUPLICATE, QOTOM_EHCI_LEGACY_OVERLAP,
    QOTOM_EHCI_LEGACY_ABSENT
};

/* Caller owns immutable nonaliasing inputs and the same serialized config/MMIO
 * mapping contracts as the capability collector. Refresh five config and three
 * MMIO dwords, then read <=48 extended headers and <=1 legacy control/status
 * dword: <=57 reads total. No write operation or ownership decision exists.
 * On failure count/legacy_offset/control_status remain zero; array staging
 * bytes are not published authority. Sequential samples are not atomic. */
static inline enum qotom_ehci_legacy_status qotom_collect_ehci_legacy(
        pci_enumeration_read config, void *config_context,
        qotom_ehci_mmio_read mmio, void *mmio_context,
        const struct pci_enumeration_header *initial,
        const struct qotom_ehci_capabilities *previous,
        struct qotom_ehci_legacy_snapshot *out) {
    if (out) {out->count=0;out->legacy_offset=0;out->control_status=0;}
    if (!config || !mmio || !initial || !previous || !out) return QOTOM_EHCI_LEGACY_ARGUMENT;
    struct qotom_ehci_capabilities fresh;
    if (qotom_collect_ehci_capabilities(config,config_context,mmio,mmio_context,initial,&fresh) != QOTOM_EHCI_OK)
        return QOTOM_EHCI_LEGACY_REFRESH;
    if (fresh.capbase != previous->capbase || fresh.structural != previous->structural ||
        fresh.capability != previous->capability) return QOTOM_EHCI_LEGACY_DRIFT;
    uint8_t offset = (uint8_t)(fresh.capability >> 8), legacy = 0;
    uint64_t visited=0;
    uint32_t count=0;
    while (offset) {
        if (offset < 64 || (offset & 3)) return QOTOM_EHCI_LEGACY_POINTER;
        uint64_t bit=UINT64_C(1)<<((offset-64)/4);
        if (visited & bit) return QOTOM_EHCI_LEGACY_CYCLE;
        if (count == QOTOM_EHCI_EXT_CAPACITY) return QOTOM_EHCI_LEGACY_POINTER;
        visited |= bit;
        uint32_t raw;
        if (!config(config_context,0,29,0,offset,&raw)) return QOTOM_EHCI_LEGACY_READ;
        uint32_t id=raw&255;
        if (id==0 || id==255) return QOTOM_EHCI_LEGACY_ID;
        if (id==1) {
            if (legacy) return QOTOM_EHCI_LEGACY_DUPLICATE;
            if (offset>248) return QOTOM_EHCI_LEGACY_POINTER;
            legacy=offset;
        }
        out->headers[count++]=(struct qotom_ehci_extended_header){offset,raw};
        offset=(uint8_t)(raw>>8);
    }
    uint32_t control=0;
    if (legacy) {
        for (uint32_t i=0;i<count;++i)
            if (out->headers[i].offset==legacy+4) return QOTOM_EHCI_LEGACY_OVERLAP;
        if (!config(config_context,0,29,0,(uint8_t)(legacy+4),&control)) return QOTOM_EHCI_LEGACY_READ;
        if (control==UINT32_MAX) return QOTOM_EHCI_LEGACY_ABSENT;
    }
    out->count=count;out->legacy_offset=legacy;out->control_status=control;
    return QOTOM_EHCI_LEGACY_OK;
}
#endif
