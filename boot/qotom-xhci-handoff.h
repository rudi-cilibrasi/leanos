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
enum qotom_xhci_verify_kind {
    QOTOM_XHCI_VERIFY_NONE, QOTOM_XHCI_VERIFY_COLLECTOR,
    QOTOM_XHCI_VERIFY_COUNT, QOTOM_XHCI_VERIFY_LEGACY_OFFSET,
    QOTOM_XHCI_VERIFY_HEADER_OFFSET, QOTOM_XHCI_VERIFY_HEADER_RAW,
    QOTOM_XHCI_VERIFY_SEMAPHORE
};
struct qotom_xhci_handoff_result {
    uint32_t write_attempted, polls, last_support, final_control;
    uint32_t verify_kind, verify_index, verify_expected, verify_observed;
};
/* J1900 datasheet 329670-002 section 14.7.138: XECP_CMDM_STS0 at 8040
 * has live RO status in bits31:20 and18:16. Bit19 is reserved; low16 hold
 * the next pointer and vendor ID. Only the identified status bits may vary
 * during the final handoff comparison. They do not prove DMA drain. */
#define QOTOM_XHCI_CMDM_STATUS UINT32_C(0xfff70000)
static inline uint32_t qotom_xhci_final_mutable_bits(
        const struct qotom_xhci_ext_header *header,uint32_t legacy_offset) {
    if(header->offset==legacy_offset)return UINT32_C(0x01010000);
    if(header->offset==0x8040 && (header->raw&0xffff)==0x0cc1)
        return QOTOM_XHCI_CMDM_STATUS;
    return 0;
}
/* Both lists are complete successful collector outputs. Report the first
 * comparison failure without extra hardware access or partial collector data. */
static inline int qotom_xhci_final_difference(const struct qotom_xhci_legacy *a,
        const struct qotom_xhci_legacy *b,struct qotom_xhci_handoff_result *out) {
    if(a->count!=b->count) {
        out->verify_kind=QOTOM_XHCI_VERIFY_COUNT;
        out->verify_expected=a->count;out->verify_observed=b->count;return 1;
    }
    if(a->legacy_offset!=b->legacy_offset) {
        out->verify_kind=QOTOM_XHCI_VERIFY_LEGACY_OFFSET;
        out->verify_expected=a->legacy_offset;out->verify_observed=b->legacy_offset;return 1;
    }
    for(uint32_t i=0;i<a->count;++i) {
        if(a->headers[i].offset!=b->headers[i].offset) {
            out->verify_kind=QOTOM_XHCI_VERIFY_HEADER_OFFSET;out->verify_index=i;
            out->verify_expected=a->headers[i].offset;out->verify_observed=b->headers[i].offset;return 1;
        }
        uint32_t mask=qotom_xhci_final_mutable_bits(&a->headers[i],a->legacy_offset);
        if((a->headers[i].raw^b->headers[i].raw)&~mask) {
            out->verify_kind=QOTOM_XHCI_VERIFY_HEADER_RAW;out->verify_index=i;
            out->verify_expected=a->headers[i].raw;out->verify_observed=b->headers[i].raw;return 1;
        }
    }
    return 0;
}
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
        enum qotom_xhci_legacy_status collected=qotom_collect_xhci_legacy(config,config_context,
            mmio,mmio_context,extended,extended_context,initial,caps,&final);
        if(collected!=QOTOM_XHCI_LEGACY_OK) {
            out->verify_kind=QOTOM_XHCI_VERIFY_COLLECTOR;out->verify_observed=collected;
            return QOTOM_XHCI_HANDOFF_FINAL;
        }
        if(qotom_xhci_final_difference(&fresh,&final,out))return QOTOM_XHCI_HANDOFF_FINAL;
        for(uint32_t j=0;j<final.count;++j)
            if(final.headers[j].offset==offset) {
                out->last_support=final.headers[j].raw;
                if((out->last_support&UINT32_C(0x01010000))!=UINT32_C(0x01000000)) {
                    out->verify_kind=QOTOM_XHCI_VERIFY_SEMAPHORE;out->verify_index=j;
                    out->verify_expected=(support&~UINT32_C(0x01010000))|UINT32_C(0x01000000);
                    out->verify_observed=out->last_support;
                    return QOTOM_XHCI_HANDOFF_FINAL;
                }
            }
        out->final_control=final.control_status;
        return QOTOM_XHCI_HANDOFF_OBSERVED;
    }
    return QOTOM_XHCI_HANDOFF_TIMEOUT;
}
#endif
