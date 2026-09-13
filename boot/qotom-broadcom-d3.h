#ifndef LEANOS_QOTOM_BROADCOM_D3_H
#define LEANOS_QOTOM_BROADCOM_D3_H
#include "pci-power-observation.h"
#include "qotom-pcie-pending.h"

#define QOTOM_BROADCOM_COMMAND_INITIAL UINT16_C(0x0006)
#define QOTOM_BROADCOM_COMMAND_DISABLED UINT16_C(0x0000)
#define QOTOM_BROADCOM_PMCSR_D0 UINT16_C(0x4008)
#define QOTOM_BROADCOM_PMCSR_D3HOT UINT16_C(0x400b)

typedef int (*qotom_broadcom_write_word)(void *,uint8_t,uint8_t,uint8_t,uint8_t,uint16_t);
struct qotom_broadcom_d3_result {
    uint32_t command_attempted,before_command,after_command;
    uint32_t pending_polls,device_status;
    uint32_t before_pmcsr,d3_attempted,after_pmcsr;
};
enum qotom_broadcom_d3_status {
    QOTOM_BROADCOM_D3_OK,QOTOM_BROADCOM_D3_ARGUMENT,QOTOM_BROADCOM_D3_PRIOR,
    QOTOM_BROADCOM_D3_REFRESH,QOTOM_BROADCOM_D3_COMMAND,
    QOTOM_BROADCOM_D3_COMMAND_WRITE,QOTOM_BROADCOM_D3_COMMAND_READBACK,
    QOTOM_BROADCOM_D3_PENDING,QOTOM_BROADCOM_D3_PM,
    QOTOM_BROADCOM_D3_PM_WRITE,QOTOM_BROADCOM_D3_PM_READBACK,
    QOTOM_BROADCOM_D3_FINAL
};

static inline int qotom_broadcom_header_valid_command(
        const struct pci_enumeration_header *h,uint16_t command) {
    return h && h->bus==2 && !h->device && !h->function &&
        h->words[0]==UINT32_C(0x435314e4) && (h->words[1]&0xffff)==command &&
        h->words[2]==UINT32_C(0x02800001) &&
        (h->words[3]&UINT32_C(0x00ff0000))==0 &&
        h->words[4]==UINT32_C(0xd0700004) && !h->words[5] &&
        h->words[11]==UINT32_C(0x04d814e4) && h->words[13]==0x40;
}
static inline int qotom_broadcom_pcie_valid(const struct pci_express_observation *p) {
    return p && p->status==PCI_EXPRESS_OK && p->offset==0xd0 &&
        p->device_capabilities==UINT32_C(0x05908fa0) &&
        p->device_control_status==UINT32_C(0x00190000);
}
static inline int qotom_broadcom_caps_valid(const struct pci_capability_snapshot *caps) {
    static const uint8_t offsets[4]={0x40,0x58,0x48,0xd0};
    static const uint32_t raws[4]={UINT32_C(0xce035801),UINT32_C(0x00784809),
        UINT32_C(0x0080d005),UINT32_C(0x00010010)};
    if(!caps || caps->count!=4)return 0;
    for(unsigned i=0;i<4;++i)
        if(caps->headers[i].offset!=offsets[i] || caps->headers[i].raw!=raws[i])return 0;
    return 1;
}
static inline int qotom_broadcom_pm_valid(const struct pci_power_observation *p,
        uint16_t pmcsr) {
    return p && p->status==PCI_POWER_OK && p->offset==0x40 &&
        p->pm_capabilities==UINT32_C(0xce03) &&
        p->control_status==pmcsr;
}
static inline int qotom_broadcom_root_prior_valid(
        const struct pci_enumeration_header *bridge,
        enum qotom_rootport_bme_status bme_status,
        const struct qotom_rootport_bme_result *bme,
        enum qotom_pcie_pending_status pending_status,
        const struct qotom_pcie_pending_result *pending) {
    return bridge && bridge->function==1 && qotom_rootport_header_valid(bridge) &&
        bridge->words[6]==UINT32_C(0x00020200) &&
        bridge->words[8]==UINT32_C(0xd070d070) &&
        bridge->words[9]==UINT32_C(0x0001fff1) && !bridge->words[10] && !bridge->words[11] &&
        bme_status==QOTOM_ROOTPORT_OK && bme &&
        bme->attempted==1 && bme->before_command==7 && bme->after_command==3 &&
        pending_status==QOTOM_PCIE_PENDING_OK && pending &&
        pending->polls>=2 && pending->polls<=QOTOM_PCIE_PENDING_POLL_LIMIT &&
        (pending->device_status&~UINT32_C(1))==UINT32_C(0x10);
}

static inline int qotom_broadcom_same_list(
        const struct pci_capability_snapshot *a,const struct pci_capability_snapshot *b) {
    return pci_express_same_list(a,b);
}
static inline int qotom_broadcom_refresh(pci_enumeration_read read,void *context,
        const struct pci_enumeration_header *initial,
        const struct pci_capability_snapshot *caps,uint16_t command,uint16_t pmcsr,
        struct pci_express_observation *pcie,struct pci_power_observation *power) {
    if(!read || !initial || !qotom_broadcom_caps_valid(caps) || !pcie || !power ||
       !qotom_broadcom_header_valid_command(initial,QOTOM_BROADCOM_COMMAND_INITIAL))return 0;
    struct pci_enumeration_header current=*initial;
    current.words[1]=(current.words[1]&UINT32_C(0xffff0000))|command;
    for(unsigned i=0;i<16;++i) {
        uint32_t raw,mask=i==1?UINT32_C(0x0010ffff):UINT32_MAX;
        if(!read(context,2,0,0,(uint8_t)(i*4),&raw) ||
           (raw&mask)!=(current.words[i]&mask))return 0;
    }
    *pcie=pci_observe_express(read,context,&current,caps);
    if(!qotom_broadcom_pcie_valid(pcie))return 0;
    *power=pci_observe_power(read,context,&current,caps);
    return qotom_broadcom_pm_valid(power,pmcsr);
}

/* The bus-2 root port has already gated upstream Memory/IO requests and
 * produced two delayed TP-clear samples. This sequence refreshes the complete
 * Broadcom identity/list/PCIe/PM state, disables I/O, memory and bus mastering
 * with Command=0000, obtains two more TP-clear samples, then requests D3hot
 * with PME disabled and verifies configuration-visible state. PCI PM 1.2
 * requires D0/D3hot support and permits only PME actions from D3hot.
 *
 * The bounded sequence does not prove posted-write completion or exclude SMM,
 * firmware or AP activity. The caller supplies serialized callbacks, exact
 * native firmware/root binding, immutable inputs and a two-write authority.
 * Failed stores may have effects; no rollback or D0 restore is attempted. */
static inline enum qotom_broadcom_d3_status qotom_broadcom_enter_d3hot(
        pci_enumeration_read read,void *context,
        qotom_broadcom_write_word write,void *writer,
        qotom_pcie_pending_delay delay,void *delay_context,
        const struct pci_enumeration_header *endpoint,
        const struct pci_enumeration_header *bridge,
        const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *prior_pcie,
        enum qotom_rootport_bme_status root_bme_status,
        const struct qotom_rootport_bme_result *root_bme,
        enum qotom_pcie_pending_status root_pending_status,
        const struct qotom_pcie_pending_result *root_pending,
        struct qotom_broadcom_d3_result *out) {
    if(out)*out=(struct qotom_broadcom_d3_result){0};
    if(!read || !write || !delay || !endpoint || !bridge || !caps ||
       !prior_pcie || !root_bme || !root_pending || !out)
        return QOTOM_BROADCOM_D3_ARGUMENT;
    if(!qotom_broadcom_header_valid_command(endpoint,QOTOM_BROADCOM_COMMAND_INITIAL) ||
       !qotom_broadcom_pcie_valid(prior_pcie) || !qotom_broadcom_caps_valid(caps) ||
       !qotom_broadcom_root_prior_valid(bridge,root_bme_status,root_bme,
            root_pending_status,root_pending))return QOTOM_BROADCOM_D3_PRIOR;
    struct pci_express_observation pcie;
    struct pci_power_observation power;
    if(!qotom_broadcom_refresh(read,context,endpoint,caps,QOTOM_BROADCOM_COMMAND_INITIAL,
            QOTOM_BROADCOM_PMCSR_D0,&pcie,&power))return QOTOM_BROADCOM_D3_REFRESH;
    uint32_t value;
    if(!read(context,2,0,0,4,&value) || (value&0xffff)!=QOTOM_BROADCOM_COMMAND_INITIAL)
        return QOTOM_BROADCOM_D3_COMMAND;
    out->before_command=QOTOM_BROADCOM_COMMAND_INITIAL;out->command_attempted=1;
    if(!write(writer,2,0,0,4,QOTOM_BROADCOM_COMMAND_DISABLED))
        return QOTOM_BROADCOM_D3_COMMAND_WRITE;
    if(!read(context,2,0,0,4,&value))return QOTOM_BROADCOM_D3_COMMAND_READBACK;
    out->after_command=value&0xffff;
    if(out->after_command!=QOTOM_BROADCOM_COMMAND_DISABLED)
        return QOTOM_BROADCOM_D3_COMMAND_READBACK;
    if(!qotom_broadcom_refresh(read,context,endpoint,caps,QOTOM_BROADCOM_COMMAND_DISABLED,
            QOTOM_BROADCOM_PMCSR_D0,&pcie,&power))return QOTOM_BROADCOM_D3_REFRESH;
    struct qotom_pcie_pending_result pending={0};
    enum qotom_pcie_pending_status ps=qotom_confirm_pcie_nonposted_quiet_command(
        read,context,delay,delay_context,endpoint,caps,prior_pcie,
        QOTOM_BROADCOM_COMMAND_DISABLED,&pending);
    out->pending_polls=pending.polls;out->device_status=pending.device_status;
    if(ps!=QOTOM_PCIE_PENDING_OK)return QOTOM_BROADCOM_D3_PENDING;
    if(!qotom_broadcom_refresh(read,context,endpoint,caps,QOTOM_BROADCOM_COMMAND_DISABLED,
            QOTOM_BROADCOM_PMCSR_D0,&pcie,&power))return QOTOM_BROADCOM_D3_PM;
    out->before_pmcsr=power.control_status&0xffff;out->d3_attempted=1;
    if(!write(writer,2,0,0,0x44,QOTOM_BROADCOM_PMCSR_D3HOT))
        return QOTOM_BROADCOM_D3_PM_WRITE;
    if(!read(context,2,0,0,0x44,&value))return QOTOM_BROADCOM_D3_PM_READBACK;
    out->after_pmcsr=value&0xffff;
    if(out->after_pmcsr!=QOTOM_BROADCOM_PMCSR_D3HOT)
        return QOTOM_BROADCOM_D3_PM_READBACK;
    struct pci_enumeration_header current=*endpoint;
    current.words[1]=(current.words[1]&UINT32_C(0xffff0000));
    struct pci_capability_snapshot final;
    if(pci_collect_capabilities(read,context,&current,&final).status!=PCI_CAPABILITY_OK ||
       !qotom_broadcom_same_list(caps,&final) ||
       !read(context,2,0,0,4,&value) || (value&0xffff)!=0 ||
       !read(context,2,0,0,0x44,&value) || (value&0xffff)!=QOTOM_BROADCOM_PMCSR_D3HOT)
        return QOTOM_BROADCOM_D3_FINAL;
    out->after_pmcsr=value&0xffff;return QOTOM_BROADCOM_D3_OK;
}
#endif
