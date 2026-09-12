#ifndef LEANOS_QOTOM_REALTEK_BME_H
#define LEANOS_QOTOM_REALTEK_BME_H
#include "qotom-realtek-route.h"

typedef int (*qotom_realtek_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_realtek_bme_result { uint32_t attempted,before_command,after_command; };
enum qotom_realtek_bme_status {
    QOTOM_REALTEK_BME_OK,QOTOM_REALTEK_BME_ARGUMENT,QOTOM_REALTEK_BME_PRIOR,
    QOTOM_REALTEK_BME_REFRESH,QOTOM_REALTEK_BME_STATE,QOTOM_REALTEK_BME_COMMAND,
    QOTOM_REALTEK_BME_WRITE,QOTOM_REALTEK_BME_READBACK,QOTOM_REALTEK_BME_FINAL
};
static inline int qotom_realtek_stopped(const struct qotom_realtek_state *state) {
    return state && state->transmit_before==state->transmit_after &&
        (state->transmit_before&UINT32_C(0x7cc00800))==UINT32_C(0x2c800800) &&
        !state->command_before && !state->command_after && !state->interrupt_mask;
}
static inline int qotom_realtek_same_state(const struct qotom_realtek_state *a,
        const struct qotom_realtek_state *b) {
    return a && b && a->transmit_before==b->transmit_before &&
        a->command_before==b->command_before && a->interrupt_mask==b->interrupt_mask &&
        a->receive==b->receive && a->command_after==b->command_after &&
        a->transmit_after==b->transmit_after;
}
/* The reviewed RTL8168E-VL Command has TX/RX/reset clear, IMR is zero and
 * TXCFG reports queue empty. Two exact 90-read routed-state collections and
 * three Command reads total 183 reads; one word write clears only BME (7->3).
 * Retain memory/I/O decoding and adjacent PCI Status. No endpoint register
 * write, acknowledgement, reset, poll or rollback. Failed writes may have
 * effects and are reported. Clear engine/queue samples and PCIe TP samples
 * remain sequential and do not establish transaction drain or continuing
 * firmware exclusion. Caller binds serialized immutable/nonaliasing inputs,
 * native firmware/root/resources and consumed word-store authority. */
static inline enum qotom_realtek_bme_status qotom_clear_realtek_bme(
        pci_enumeration_read config,void *config_context,
        qotom_realtek_mmio_read mmio,void *mmio_context,
        qotom_realtek_write_word write,void *write_context,
        const struct pci_enumeration_header *endpoint,
        const struct pci_enumeration_header *bridge,const struct pci_capability_snapshot *caps,
        enum qotom_rootport_bme_status route_status,const struct qotom_rootport_bme_result *route,
        enum qotom_realtek_status prior_status,const struct qotom_realtek_state *prior,
        struct qotom_realtek_bme_result *out) {
    if(out)*out=(struct qotom_realtek_bme_result){0};
    if(!config || !mmio || !write || !endpoint || !bridge || !caps || !route || !prior || !out)
        return QOTOM_REALTEK_BME_ARGUMENT;
    if(prior_status!=QOTOM_REALTEK_OK || !qotom_realtek_stopped(prior) ||
       !qotom_realtek_route_valid(endpoint,bridge,route_status,route))
        return QOTOM_REALTEK_BME_PRIOR;
    struct qotom_realtek_state fresh={0};
    if(qotom_collect_realtek_routed_state(config,config_context,mmio,mmio_context,
            endpoint,bridge,caps,route_status,route,&fresh)!=QOTOM_REALTEK_OK)
        return QOTOM_REALTEK_BME_REFRESH;
    if(!qotom_realtek_stopped(&fresh) || !qotom_realtek_same_state(prior,&fresh))
        return QOTOM_REALTEK_BME_STATE;
    uint32_t command;
    if(!config(config_context,endpoint->bus,0,0,4,&command) || (command&0xffff)!=7)
        return QOTOM_REALTEK_BME_COMMAND;
    out->before_command=7;out->attempted=1;
    if(!write(write_context,endpoint->bus,0,0,4,3))return QOTOM_REALTEK_BME_WRITE;
    if(!config(config_context,endpoint->bus,0,0,4,&command))return QOTOM_REALTEK_BME_READBACK;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_REALTEK_BME_READBACK;
    struct pci_enumeration_header final=*endpoint;
    final.words[1]=(final.words[1]&UINT32_C(0xffff0000))|3;
    if(qotom_collect_realtek_routed_state_command(config,config_context,mmio,mmio_context,
            &final,bridge,caps,route_status,route,3,&fresh)!=QOTOM_REALTEK_OK ||
       !qotom_realtek_stopped(&fresh) || !qotom_realtek_same_state(prior,&fresh))
        return QOTOM_REALTEK_BME_FINAL;
    if(!config(config_context,endpoint->bus,0,0,4,&command))return QOTOM_REALTEK_BME_FINAL;
    out->after_command=command&0xffff;
    if(out->after_command!=3)return QOTOM_REALTEK_BME_FINAL;
    return QOTOM_REALTEK_BME_OK;
}
#endif
