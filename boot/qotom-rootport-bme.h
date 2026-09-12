#ifndef LEANOS_QOTOM_ROOTPORT_BME_H
#define LEANOS_QOTOM_ROOTPORT_BME_H
#include "pci-express-observation.h"
typedef int (*qotom_rootport_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_rootport_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_rootport_bme_status {
    QOTOM_ROOTPORT_OK,QOTOM_ROOTPORT_ARGUMENT,QOTOM_ROOTPORT_PRIOR,
    QOTOM_ROOTPORT_REFRESH,QOTOM_ROOTPORT_COMMAND,QOTOM_ROOTPORT_WRITE,
    QOTOM_ROOTPORT_READBACK,QOTOM_ROOTPORT_FINAL
};
static inline int qotom_rootport_sample_valid(const struct pci_express_observation *p) {
    return p && p->status==PCI_EXPRESS_OK && p->offset==0x40 &&
        p->device_capabilities==UINT32_C(0x8000) &&
        !(p->device_control_status&~UINT32_C(0x001f0000));
}
static inline int qotom_rootport_header_valid(const struct pci_enumeration_header *header) {
    return header && !(header->bus || header->device!=28 || header->function>3 ||
       header->words[0]!=(UINT32_C(0x0f488086)+(uint32_t)header->function*UINT32_C(0x20000)) ||
       header->words[2]!=UINT32_C(0x0604000e) ||
       (header->words[3]&UINT32_C(0x00ff0000))!=UINT32_C(0x00810000) ||
       (header->words[1]&0xffff)!=7);
}
/* The raw bridge routing header must remain stable. Exclude only primary and
 * secondary Status bits, retaining the primary capability-list indicator. */
static inline int qotom_rootport_refresh(pci_enumeration_read read,void *ctx,
        const struct pci_enumeration_header *header,const struct pci_capability_snapshot *caps) {
    for(unsigned i=0;i<16;++i) {
        uint32_t raw,mask=i==1?UINT32_C(0x0010ffff):i==7?UINT32_C(0xffff):UINT32_MAX;
        if(!read(ctx,0,28,header->function,(uint8_t)(i*4),&raw) ||
           (raw&mask)!=(header->words[i]&mask))return 0;
    }
    struct pci_express_observation p=pci_observe_express(read,ctx,header,caps);
    return qotom_rootport_sample_valid(&p);
}
/* Intel329670-002 17.6.2: BME gates upstream Memory/IO requests, not
 * completions or other requests. One word0003 clears only BME. Two complete
 * header/PCIe refreshes plus three Command reads: <=247 reads, one write.
 * Clear TP samples do not establish drain. No endpoint stop/reset, link write,
 * polling or rollback. Failed writes may have effects. Caller supplies exact
 * native inventory, firmware/root binding, immutable nonaliasing observations
 * and serialized bounded callbacks. This experiment is not DMA admission. */
static inline enum qotom_rootport_bme_status qotom_clear_rootport_bme(
        pci_enumeration_read read,void *ctx,qotom_rootport_write_word write,void *writer,
        const struct pci_enumeration_header *header,const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *prior,struct qotom_rootport_bme_result *out) {
    if(out)*out=(struct qotom_rootport_bme_result){0};
    if(!read || !write || !header || !caps || !prior || !out)return QOTOM_ROOTPORT_ARGUMENT;
    if(!qotom_rootport_header_valid(header) || !qotom_rootport_sample_valid(prior))return QOTOM_ROOTPORT_PRIOR;
    if(!qotom_rootport_refresh(read,ctx,header,caps))return QOTOM_ROOTPORT_REFRESH;
    uint32_t command;
    if(!read(ctx,0,28,header->function,4,&command) || (command&0xffff)!=7)return QOTOM_ROOTPORT_COMMAND;
    out->before_command=7;out->attempted=1;
    if(!write(writer,0,28,header->function,4,3))return QOTOM_ROOTPORT_WRITE;
    if(!read(ctx,0,28,header->function,4,&command))return QOTOM_ROOTPORT_READBACK;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_ROOTPORT_READBACK;
    struct pci_enumeration_header final=*header;
    final.words[1]=(final.words[1]&UINT32_C(0xffff0000))|3;
    if(!qotom_rootport_refresh(read,ctx,&final,caps))return QOTOM_ROOTPORT_FINAL;
    if(!read(ctx,0,28,header->function,4,&command))return QOTOM_ROOTPORT_FINAL;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_ROOTPORT_FINAL;
    return QOTOM_ROOTPORT_OK;
}
#endif
