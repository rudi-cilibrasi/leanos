#ifndef LEANOS_QOTOM_TXE_BME_H
#define LEANOS_QOTOM_TXE_BME_H
#include "qotom-txe-status.h"

typedef int (*qotom_txe_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_txe_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_txe_bme_status {
    QOTOM_TXE_BME_OK,QOTOM_TXE_BME_ARGUMENT,QOTOM_TXE_BME_PRIOR,
    QOTOM_TXE_BME_REFRESH,QOTOM_TXE_BME_STATE,QOTOM_TXE_BME_COMMAND,
    QOTOM_TXE_BME_WRITE,QOTOM_TXE_BME_READBACK,QOTOM_TXE_BME_FINAL
};
static inline int qotom_txe_same_status(const struct qotom_txe_status_observation *a,
        const struct qotom_txe_status_observation *b) {
    return a && b && a->firmware0==b->firmware0 && a->firmware1==b->firmware1;
}

/* Refresh the retained firmware-status observation, clear only host-visible
 * PCI Command.BME (0106 to 0102), and refresh status again. This performs 23
 * configuration reads and one exact 16-bit write. It preserves MSE and INTx
 * disable. The readback controls the PCI function's ordinary bus-master
 * permission; it is not evidence that the TXE-private DMA engine is stopped,
 * drained, or host-controlled. Firmware noninterference remains an explicit
 * platform assumption. A failed write may have effects; there is no rollback. */
static inline enum qotom_txe_bme_status qotom_clear_txe_bme(
        pci_enumeration_read read,void *read_context,
        qotom_txe_write_word write,void *write_context,
        const struct pci_enumeration_header *endpoint,
        enum qotom_txe_status prior_status,
        const struct qotom_txe_status_observation *prior,
        struct qotom_txe_bme_result *out) {
    if(out)*out=(struct qotom_txe_bme_result){0};
    if(!read || !write || !endpoint || !prior || !out)
        return QOTOM_TXE_BME_ARGUMENT;
    if(prior_status!=QOTOM_TXE_OK)return QOTOM_TXE_BME_PRIOR;
    struct qotom_txe_status_observation fresh={0};
    if(qotom_collect_txe_status(read,read_context,endpoint,&fresh)!=QOTOM_TXE_OK)
        return QOTOM_TXE_BME_REFRESH;
    if(!qotom_txe_same_status(prior,&fresh))return QOTOM_TXE_BME_STATE;
    uint32_t command;
    if(!read(read_context,0,26,0,4,&command) ||
       (command&UINT32_C(0xffff))!=UINT32_C(0x0106))
        return QOTOM_TXE_BME_COMMAND;
    out->attempted=1;out->before_command=UINT32_C(0x0106);
    if(!write(write_context,0,26,0,4,UINT16_C(0x0102)))
        return QOTOM_TXE_BME_WRITE;
    if(!read(read_context,0,26,0,4,&command))return QOTOM_TXE_BME_READBACK;
    out->after_command=command&UINT32_C(0xffff);
    if(out->after_command!=UINT32_C(0x0102))return QOTOM_TXE_BME_READBACK;
    struct pci_enumeration_header final=*endpoint;
    final.words[1]=(final.words[1]&UINT32_C(0xffff0000))|UINT32_C(0x0102);
    if(qotom_collect_txe_status_command(read,read_context,&final,UINT16_C(0x0102),
            &fresh)!=QOTOM_TXE_OK || !qotom_txe_same_status(prior,&fresh))
        return QOTOM_TXE_BME_FINAL;
    if(!read(read_context,0,26,0,4,&command))return QOTOM_TXE_BME_FINAL;
    out->after_command=command&UINT32_C(0xffff);
    return out->after_command==UINT32_C(0x0102)?QOTOM_TXE_BME_OK:QOTOM_TXE_BME_FINAL;
}
#endif
