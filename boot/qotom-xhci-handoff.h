#ifndef LEANOS_QOTOM_XHCI_HANDOFF_H
#define LEANOS_QOTOM_XHCI_HANDOFF_H
#include "qotom-xhci-legacy.h"
#define QOTOM_XHCI_HANDOFF_POLLS 100u
typedef int (*qotom_xhci_write_dword)(void *,uint64_t,uint32_t);
typedef int (*qotom_xhci_delay_ms)(void *,uint32_t);
enum qotom_xhci_handoff_status {
    QOTOM_XHCI_HANDOFF_OBSERVED, QOTOM_XHCI_HANDOFF_ARGUMENT,
    QOTOM_XHCI_HANDOFF_REFRESH, QOTOM_XHCI_HANDOFF_DRIFT,
    QOTOM_XHCI_HANDOFF_INITIAL, QOTOM_XHCI_HANDOFF_WRITE,
    QOTOM_XHCI_HANDOFF_DELAY, QOTOM_XHCI_HANDOFF_READ,
    QOTOM_XHCI_HANDOFF_CHANGED, QOTOM_XHCI_HANDOFF_TIMEOUT,
    QOTOM_XHCI_HANDOFF_FINAL
};
struct qotom_xhci_handoff_result {
    uint32_t write_attempted, polls, last_support, final_control;
};
/* Complete list equality, optionally allowing only the legacy semaphore bits
 * to change. Both inputs must have come from successful collectors. */
static inline int qotom_xhci_same_legacy(
        const struct qotom_xhci_legacy *a,
        const struct qotom_xhci_legacy *b, uint32_t mutable_bits) {
    if(a->count>QOTOM_XHCI_EXT_LIMIT || a->count!=b->count ||
       a->legacy_offset!=b->legacy_offset)return 0;
    for(uint32_t i=0;i<a->count;++i) {
        uint32_t mask=a->headers[i].offset==a->legacy_offset ? mutable_bits : 0;
        if(a->headers[i].offset!=b->headers[i].offset ||
           ((a->headers[i].raw^b->headers[i].raw)&~mask))return 0;
    }
    return 1;
}
/* Callback candidate only; no native write backend is authorized here.
 * Immutable, nonaliasing inputs, serialized accesses, stable PCI resources and
 * bounded callbacks are caller obligations. Delay must wait the requested real
 * milliseconds or fail. At most 274 reads (two <=87-read collectors plus 100
 * polls), one DWORD MMIO write, and 100 ten-ms delays. No BIOS semaphore clear, SMI
 * control change, reset, rollback or operational-register access exists.
 * Output is diagnostic on EVERY status, never DMA/firmware-exclusion authority.
 * A failed write can have taken effect: write_attempted records that ambiguity.
 */
static inline enum qotom_xhci_handoff_status qotom_request_xhci_handoff(
        pci_enumeration_read config, void *config_context,
        qotom_xhci_mmio_read mmio, void *mmio_context,
        qotom_xhci_mmio_read extended, void *extended_context,
        qotom_xhci_write_dword write_dword, void *write_context,
        qotom_xhci_delay_ms delay, void *delay_context,
        const struct pci_enumeration_header *initial,
        const struct qotom_xhci_capabilities *caps,
        const struct qotom_xhci_legacy *previous,
        struct qotom_xhci_handoff_result *out) {
    if(out)*out=(struct qotom_xhci_handoff_result){0};
    if(!config || !mmio || !extended || !write_dword || !delay || !initial || !caps || !previous || !out)
        return QOTOM_XHCI_HANDOFF_ARGUMENT;
    struct qotom_xhci_legacy fresh={0};
    if(qotom_collect_xhci_legacy(config,config_context,mmio,mmio_context,extended,extended_context,initial,caps,&fresh)!=QOTOM_XHCI_LEGACY_OK)
        return QOTOM_XHCI_HANDOFF_REFRESH;
    if(!qotom_xhci_same_legacy(previous,&fresh,0) || previous->control_status!=fresh.control_status)
        return QOTOM_XHCI_HANDOFF_DRIFT;
    uint32_t offset=fresh.legacy_offset;
    uint32_t support=0;
    for(uint32_t i=0;i<fresh.count;++i)
        if(fresh.headers[i].offset==offset)support=fresh.headers[i].raw;
    /* Closed initial state: BIOS-owned, OS-clear, reserved semaphore bits zero.
     * The collector has already checked ID, links, uniqueness and nonoverlap. */
    if(!offset || (support&UINT32_C(0xffff0000))!=UINT32_C(0x00010000))
        return QOTOM_XHCI_HANDOFF_INITIAL;
    uint64_t address;
    if(!qotom_xhci_extended_address(offset,&address))return QOTOM_XHCI_HANDOFF_INITIAL;
    out->last_support=support;
    out->write_attempted=1;
    if(!write_dword(write_context,address,support|UINT32_C(0x01000000)))return QOTOM_XHCI_HANDOFF_WRITE;
    for(uint32_t i=0;i<QOTOM_XHCI_HANDOFF_POLLS;++i) {
        if(!delay(delay_context,10))return QOTOM_XHCI_HANDOFF_DELAY;
        ++out->polls;
        uint32_t raw;
        if(!extended(extended_context,address,&raw))return QOTOM_XHCI_HANDOFF_READ;
        out->last_support=raw;
        if((raw&~UINT32_C(0x01010000))!=(support&~UINT32_C(0x01010000)) ||
           !(raw&UINT32_C(0x01000000)))return QOTOM_XHCI_HANDOFF_CHANGED;
        if(raw&UINT32_C(0x00010000))continue;
        struct qotom_xhci_legacy final={0};
        if(qotom_collect_xhci_legacy(config,config_context,mmio,mmio_context,extended,extended_context,initial,caps,&final)!=QOTOM_XHCI_LEGACY_OK ||
           !qotom_xhci_same_legacy(&fresh,&final,UINT32_C(0x01010000)))
            return QOTOM_XHCI_HANDOFF_FINAL;
        for(uint32_t j=0;j<final.count;++j)
            if(final.headers[j].offset==offset) {
                out->last_support=final.headers[j].raw;
                if((out->last_support&UINT32_C(0x01010000))!=UINT32_C(0x01000000))
                    return QOTOM_XHCI_HANDOFF_FINAL;
            }
        out->final_control=final.control_status;
        return QOTOM_XHCI_HANDOFF_OBSERVED;
    }
    return QOTOM_XHCI_HANDOFF_TIMEOUT;
}
#endif
