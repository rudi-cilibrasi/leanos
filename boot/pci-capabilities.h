#ifndef LEANOS_PCI_CAPABILITIES_H
#define LEANOS_PCI_CAPABILITIES_H
#include <stdint.h>
#include "pci-enumeration.h"

/* Conventional configuration space only: 48 aligned slots in [0x40,0xfc].
 * This observes capability headers, not capability payloads or DMA safety. */
#define PCI_CAPABILITY_CAPACITY 48u
struct pci_capability_header { uint8_t offset; uint32_t raw; };
struct pci_capability_snapshot {
    uint32_t count;
    struct pci_capability_header headers[PCI_CAPABILITY_CAPACITY];
};
enum pci_capability_status {
    PCI_CAPABILITY_OK, PCI_CAPABILITY_ARGUMENT, PCI_CAPABILITY_READ_FAILED,
    PCI_CAPABILITY_HEADER_CHANGED, PCI_CAPABILITY_POINTER,
    PCI_CAPABILITY_CYCLE, PCI_CAPABILITY_ABSENT
};
struct pci_capability_result { enum pci_capability_status status; uint8_t offset; };

/* The caller owns an immutable initial header and serialized read callback.
 * Rechecking identity, layout and list head detects drift at the beginning;
 * it cannot make the following hardware reads an atomic snapshot.
 * Failed traversals publish count zero. Only successful, terminated lists
 * expose their full count; staging bytes on failure are not authority. */
static inline struct pci_capability_result pci_collect_capabilities(
        pci_enumeration_read read, void *context,
        const struct pci_enumeration_header *initial,
        struct pci_capability_snapshot *snapshot) {
    struct pci_capability_result out = {PCI_CAPABILITY_ARGUMENT,0};
    if (snapshot) snapshot->count=0;
    if (!read || !initial || !snapshot || initial->device>31 || initial->function>7 ||
        ((initial->words[3]>>16)&0x7f)>1 || (initial->words[0]&0xffff)==0xffff)
        return out;
    const uint8_t offsets[4]={0,4,12,52};
    const uint32_t masks[4]={UINT32_MAX,UINT32_C(0x00100000),UINT32_C(0x00ff0000),255};
    for (uint32_t i=0;i<4;++i) {
        uint32_t value;
        out.offset=offsets[i];
        if (!read(context,initial->bus,initial->device,initial->function,offsets[i],&value)) {
            out.status=PCI_CAPABILITY_READ_FAILED;return out;
        }
        if ((value&masks[i])!=(initial->words[offsets[i]/4]&masks[i])) {
            out.status=PCI_CAPABILITY_HEADER_CHANGED;return out;
        }
    }
    uint32_t count=0;
    uint64_t seen=0;
    uint8_t offset=(initial->words[1]&UINT32_C(0x00100000)) ?
        (uint8_t)initial->words[13] : 0;
    while (offset) {
        out.offset=offset;
        if (offset<64 || (offset&3)) {out.status=PCI_CAPABILITY_POINTER;return out;}
        const uint64_t bit=UINT64_C(1)<<((offset-64)/4);
        if (seen&bit) {out.status=PCI_CAPABILITY_CYCLE;return out;}
        /* Unique valid pointers imply <=48 reads. Keep the explicit array
           guard even if a future change weakens pointer/cycle validation. */
        if (count==PCI_CAPABILITY_CAPACITY) {out.status=PCI_CAPABILITY_POINTER;return out;}
        seen|=bit;
        uint32_t raw;
        if (!read(context,initial->bus,initial->device,initial->function,offset,&raw)) {
            out.status=PCI_CAPABILITY_READ_FAILED;return out;
        }
        if ((raw&255)==255) {out.status=PCI_CAPABILITY_ABSENT;return out;}
        snapshot->headers[count++]=(struct pci_capability_header){offset,raw};
        offset=(uint8_t)(raw>>8);
    }
    snapshot->count=count;
    out.status=PCI_CAPABILITY_OK;out.offset=0;
    return out;
}
#endif
