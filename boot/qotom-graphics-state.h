#ifndef LEANOS_QOTOM_GRAPHICS_STATE_H
#define LEANOS_QOTOM_GRAPHICS_STATE_H
#include "pci-enumeration.h"

#define QOTOM_GRAPHICS_BAR0 UINT64_C(0xd0000000)
#define QOTOM_GRAPHICS_BAR0_SIZE UINT64_C(0x00400000)
#define QOTOM_GRAPHICS_BAR2 UINT64_C(0xc0000000)
#define QOTOM_GRAPHICS_BAR2_SIZE UINT64_C(0x10000000)
#define QOTOM_GRAPHICS_ENGINE_COUNT 3u
#define QOTOM_GRAPHICS_REGISTER_COUNT 5u
#define QOTOM_GRAPHICS_SAMPLE_WORDS 30u

typedef int (*qotom_graphics_mmio_read)(void *,uint64_t,uint32_t *);
struct qotom_graphics_state { uint32_t words[QOTOM_GRAPHICS_SAMPLE_WORDS]; };
enum qotom_graphics_status {
    QOTOM_GRAPHICS_OK,QOTOM_GRAPHICS_ARGUMENT,QOTOM_GRAPHICS_HEADER,
    QOTOM_GRAPHICS_CONFIG_READ,QOTOM_GRAPHICS_DRIFT,
    QOTOM_GRAPHICS_MMIO_READ,QOTOM_GRAPHICS_ABSENT
};

static inline int qotom_graphics_header_valid_command(
        const struct pci_enumeration_header *h,uint16_t command) {
    return h && !h->bus && h->device==2 && !h->function &&
        h->words[0]==UINT32_C(0x0f318086) &&
        (h->words[1]&UINT32_C(0xffff))==command &&
        h->words[2]==UINT32_C(0x0300000e) &&
        !(h->words[3]&UINT32_C(0x00ff0000)) &&
        h->words[4]==UINT32_C(0xd0000000) && !h->words[5] &&
        h->words[6]==UINT32_C(0xc0000008) && !h->words[7] &&
        h->words[8]==UINT32_C(0x0000f081) && !h->words[9] && !h->words[10] &&
        h->words[11]==UINT32_C(0x0f318086) && !h->words[12] &&
        h->words[13]==UINT32_C(0x000000d0) && !h->words[14] &&
        (h->words[15]&UINT32_C(0xffffff00))==UINT32_C(0x00000100);
}
static inline int qotom_graphics_header_valid(const struct pci_enumeration_header *h) {
    return qotom_graphics_header_valid_command(h,7);
}

/* Valleyview exposes RCS, VCS and BCS at BAR0+2000, +12000 and +22000.
 * Each ring contributes TAIL, HEAD, START, CTL and MI_MODE. Address selection
 * grants no mapping or access authority. */
static inline int qotom_graphics_state_address(unsigned engine,unsigned reg,
        uint64_t *out) {
    static const uint32_t engines[QOTOM_GRAPHICS_ENGINE_COUNT]={0x2000,0x12000,0x22000};
    static const uint32_t registers[QOTOM_GRAPHICS_REGISTER_COUNT]={0x30,0x34,0x38,0x3c,0x9c};
    if(!out || engine>=QOTOM_GRAPHICS_ENGINE_COUNT ||
       reg>=QOTOM_GRAPHICS_REGISTER_COUNT)return 0;
    *out=QOTOM_GRAPHICS_BAR0+engines[engine]+registers[reg];return 1;
}

/* Thirty-two exact PCI-header reads bracket two ordered fifteen-register MMIO
 * samples. This is read-only evidence: it does not stop rings, acknowledge
 * interrupts, change PCI command bits, drain DMA or establish firmware/AP
 * exclusion. The caller supplies immutable nonaliasing inputs and bound,
 * supervisor-only UC read authority. Every failed observation publishes zero. */
static inline enum qotom_graphics_status qotom_collect_graphics_state_command(
        pci_enumeration_read config,void *config_context,
        qotom_graphics_mmio_read mmio,void *mmio_context,
        const struct pci_enumeration_header *initial,uint16_t command,
        struct qotom_graphics_state *out) {
    if(out)*out=(struct qotom_graphics_state){0};
    if(!config || !mmio || !initial || !out)return QOTOM_GRAPHICS_ARGUMENT;
    if(!qotom_graphics_header_valid_command(initial,command))return QOTOM_GRAPHICS_HEADER;
    uint32_t values[QOTOM_GRAPHICS_SAMPLE_WORDS];
    for(unsigned phase=0;phase<2;++phase) {
        if(phase) {
            for(unsigned sample=0;sample<2;++sample)
                for(unsigned engine=0;engine<QOTOM_GRAPHICS_ENGINE_COUNT;++engine)
                    for(unsigned reg=0;reg<QOTOM_GRAPHICS_REGISTER_COUNT;++reg) {
                        unsigned index=sample*15+engine*5+reg;uint64_t address;
                        if(!qotom_graphics_state_address(engine,reg,&address))
                            return QOTOM_GRAPHICS_ARGUMENT;
                        if(!mmio(mmio_context,address,&values[index]))
                            return QOTOM_GRAPHICS_MMIO_READ;
                        if(values[index]==UINT32_MAX)return QOTOM_GRAPHICS_ABSENT;
                    }
        }
        for(unsigned i=0;i<16;++i) {
            uint32_t raw,mask=i==1?UINT32_C(0x0000ffff):
                (i==15?UINT32_C(0xffffff00):UINT32_MAX);
            if(!config(config_context,0,2,0,(uint8_t)(4*i),&raw))
                return QOTOM_GRAPHICS_CONFIG_READ;
            if((raw&mask)!=(initial->words[i]&mask))return QOTOM_GRAPHICS_DRIFT;
        }
    }
    for(unsigned i=0;i<QOTOM_GRAPHICS_SAMPLE_WORDS;++i)out->words[i]=values[i];
    return QOTOM_GRAPHICS_OK;
}
static inline enum qotom_graphics_status qotom_collect_graphics_state(
        pci_enumeration_read config,void *config_context,
        qotom_graphics_mmio_read mmio,void *mmio_context,
        const struct pci_enumeration_header *initial,
        struct qotom_graphics_state *out) {
    return qotom_collect_graphics_state_command(config,config_context,mmio,
        mmio_context,initial,7,out);
}
#endif
