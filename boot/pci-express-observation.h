#ifndef LEANOS_PCI_EXPRESS_OBSERVATION_H
#define LEANOS_PCI_EXPRESS_OBSERVATION_H
#include "pci-capabilities.h"

/* Read-only observation for the v1/v2 endpoints and root ports used by Qotom.
 * Immutable, nonaliasing inputs and serialized config access are caller duties.
 * No reset, polling, drain or DMA-admission decision is made here. */
enum pci_express_status {
    PCI_EXPRESS_OK, PCI_EXPRESS_NOT_PRESENT, PCI_EXPRESS_ARGUMENT,
    PCI_EXPRESS_COLLECTION_FAILED, PCI_EXPRESS_LIST_CHANGED,
    PCI_EXPRESS_SHAPE, PCI_EXPRESS_READ_FAILED, PCI_EXPRESS_ABSENT,
    PCI_EXPRESS_FINAL_FAILED
};
struct pci_express_observation {
    enum pci_express_status status;
    uint8_t offset;
    uint32_t device_capabilities;
    uint32_t device_control_status;
};
static inline int pci_express_same_list(const struct pci_capability_snapshot *a,
                                       const struct pci_capability_snapshot *b) {
    if (a->count != b->count) return 0;
    for (uint32_t i=0; i<a->count; ++i)
        if (a->headers[i].offset != b->headers[i].offset ||
            a->headers[i].raw != b->headers[i].raw) return 0;
    return 1;
}
/* Two complete identity/list collections bracket two payload reads. Upper
 * bound 106 reads (2*(4+48)+2); success can use at most 46 list slots because
 * the two payload slots may not contain a capability header, hence 102 reads.
 * Final collection checks identity/list, not atomicity or payload stability. */
static inline struct pci_express_observation pci_observe_express(
        pci_enumeration_read read, void *context,
        const struct pci_enumeration_header *initial,
        const struct pci_capability_snapshot *previous) {
    struct pci_express_observation out = {PCI_EXPRESS_ARGUMENT,0,0,0};
    if (!read || !initial || !previous || previous->count>PCI_CAPABILITY_CAPACITY)
        return out;
    struct pci_capability_snapshot fresh, final;
    if (pci_collect_capabilities(read,context,initial,&fresh).status != PCI_CAPABILITY_OK) {
        out.status=PCI_EXPRESS_COLLECTION_FAILED; return out;
    }
    if (!pci_express_same_list(&fresh,previous)) {
        out.status=PCI_EXPRESS_LIST_CHANGED; return out;
    }
    uint32_t selected=PCI_CAPABILITY_CAPACITY;
    for (uint32_t i=0; i<fresh.count; ++i) {
        if ((fresh.headers[i].raw&255)!=0x10) continue;
        if (selected!=PCI_CAPABILITY_CAPACITY) {out.status=PCI_EXPRESS_SHAPE; return out;}
        selected=i;
    }
    if (selected==PCI_CAPABILITY_CAPACITY) {out.status=PCI_EXPRESS_NOT_PRESENT; return out;}
    const struct pci_capability_header *cap=&fresh.headers[selected];
    uint32_t flags=cap->raw>>16, version=flags&15, type=(flags>>4)&15;
    uint32_t layout=(initial->words[3]>>16)&0x7f;
    /* Explicit old-device scope: no FLIT or bit14 extension, endpoint slot,
     * unknown version/type, or mismatch with the standard header layout. */
    if ((version!=1 && version!=2) || (flags&0xc000) || cap->offset>244 ||
        !((layout==0 && (type==0 || type==1) && !(flags&0x100)) ||
          (layout==1 && type==4))) {
        out.status=PCI_EXPRESS_SHAPE; return out;
    }
    for (uint32_t i=0; i<fresh.count; ++i)
        if (fresh.headers[i].offset==cap->offset+4 ||
            fresh.headers[i].offset==cap->offset+8) {
            out.status=PCI_EXPRESS_SHAPE; return out;
        }
    uint32_t payload[2];
    for (uint32_t i=0; i<2; ++i) {
        if (!read(context,initial->bus,initial->device,initial->function,
                  (uint8_t)(cap->offset+4+4*i),&payload[i])) {
            out.status=PCI_EXPRESS_READ_FAILED; return out;
        }
        if (payload[i]==UINT32_MAX) {out.status=PCI_EXPRESS_ABSENT; return out;}
    }
    if (pci_collect_capabilities(read,context,initial,&final).status != PCI_CAPABILITY_OK ||
        !pci_express_same_list(&fresh,&final)) {
        out.status=PCI_EXPRESS_FINAL_FAILED; return out;
    }
    out.status=PCI_EXPRESS_OK; out.offset=cap->offset;
    out.device_capabilities=payload[0]; out.device_control_status=payload[1];
    return out;
}
#endif
