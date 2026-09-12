#ifndef LEANOS_QOTOM_REALTEK_STATE_H
#define LEANOS_QOTOM_REALTEK_STATE_H
#include "pci-enumeration.h"

typedef int (*qotom_realtek_mmio_read)(void *,uint64_t,uint8_t,uint32_t *);
struct qotom_realtek_state {
    uint32_t transmit_before,command_before,interrupt_mask,receive,command_after,transmit_after;
};
enum qotom_realtek_status {
    QOTOM_REALTEK_OK,QOTOM_REALTEK_ARGUMENT,QOTOM_REALTEK_HEADER,
    QOTOM_REALTEK_CONFIG_READ,QOTOM_REALTEK_DRIFT,QOTOM_REALTEK_MMIO_READ,
    QOTOM_REALTEK_ABSENT,QOTOM_REALTEK_WIDTH,QOTOM_REALTEK_REVISION,QOTOM_REALTEK_RESET
};
static inline uint64_t qotom_realtek_bar(uint8_t bus) {
    return bus==1?UINT64_C(0xd0804000):(bus==3?UINT64_C(0xd0604000):0);
}
/* Address selection alone grants no mapping/access authority. */
static inline int qotom_realtek_state_address(uint8_t bus,uint32_t offset,uint8_t width,uint64_t *out) {
    uint64_t bar=qotom_realtek_bar(bus);
    if (!out || !bar || !((offset==0x37 && width==1) ||
        (offset==0x3c && width==2) || ((offset==0x40 || offset==0x44) && width==4))) return 0;
    *out=bar+offset;return 1;
}
static inline int qotom_realtek_header_valid(const struct pci_enumeration_header *h) {
    if (!h) return 0;
    uint64_t bar=qotom_realtek_bar(h->bus);
    return bar && !h->device && !h->function && h->words[0]==UINT32_C(0x816810ec) &&
        h->words[2]==UINT32_C(0x02000007) && !(h->words[3]&UINT32_C(0x00ff0000)) &&
        (h->words[1]&UINT32_C(0xffff))==7 && h->words[6]==(bar|4) && !h->words[7] &&
        h->words[8]==((bar-UINT64_C(0x4000))|12) && !h->words[9];
}
/* Eight config reads bracket six typed MMIO reads: exactly 22 on success.
 * TXCFG identifies RTL8168E-VL before other MMIO and again last. No reset,
 * stop, interrupt acknowledgement, polling, DMA/drain or atomicity claim.
 * Caller supplies immutable nonaliasing inputs and bound UC/root/resource/
 * bridge-routing access authority. Every failed observation publishes zero. */
static inline enum qotom_realtek_status qotom_collect_realtek_state(
        pci_enumeration_read config,void *config_context,
        qotom_realtek_mmio_read mmio,void *mmio_context,
        const struct pci_enumeration_header *initial,struct qotom_realtek_state *out) {
    if (out) *out=(struct qotom_realtek_state){0};
    if (!config || !mmio || !initial || !out) return QOTOM_REALTEK_ARGUMENT;
    if (!qotom_realtek_header_valid(initial)) return QOTOM_REALTEK_HEADER;
    const uint8_t offsets[8]={0,4,8,12,24,28,32,36};
    const uint32_t masks[8]={UINT32_MAX,65535,UINT32_MAX,UINT32_C(0x00ff0000),
        UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX};
    const uint8_t registers[6]={0x40,0x37,0x3c,0x44,0x37,0x40},widths[6]={4,1,2,4,1,4};
    uint32_t values[6];
    for (uint32_t phase=0;phase<2;++phase) {
        for (uint32_t i=0;i<8;++i) {
            uint32_t raw;
            if (!config(config_context,initial->bus,0,0,offsets[i],&raw)) return QOTOM_REALTEK_CONFIG_READ;
            if ((raw&masks[i])!=(initial->words[offsets[i]/4]&masks[i])) return QOTOM_REALTEK_DRIFT;
        }
        if (!phase) for (uint32_t i=0;i<6;++i) {
            uint64_t address;
            if (!qotom_realtek_state_address(initial->bus,registers[i],widths[i],&address)) return QOTOM_REALTEK_ARGUMENT;
            if (!mmio(mmio_context,address,widths[i],&values[i])) return QOTOM_REALTEK_MMIO_READ;
            uint32_t maximum=widths[i]==4?UINT32_MAX:(widths[i]==2?65535:255);
            if (values[i]>maximum) return QOTOM_REALTEK_WIDTH;
            if (values[i]==maximum) return QOTOM_REALTEK_ABSENT;
            if ((i==0 || i==5) && (values[i]&UINT32_C(0x7cc00000))!=UINT32_C(0x2c800000))
                return QOTOM_REALTEK_REVISION;
            if ((i==1 || i==4) && (values[i]&16)) return QOTOM_REALTEK_RESET;
        }
    }
    *out=(struct qotom_realtek_state){values[0],values[1],values[2],values[3],values[4],values[5]};
    return QOTOM_REALTEK_OK;
}
#endif
