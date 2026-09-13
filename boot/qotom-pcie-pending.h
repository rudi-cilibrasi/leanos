#ifndef LEANOS_QOTOM_PCIE_PENDING_H
#define LEANOS_QOTOM_PCIE_PENDING_H
#include "qotom-realtek-bme.h"

#define QOTOM_PCIE_PENDING_POLL_LIMIT 100u
#define QOTOM_PCIE_PENDING_DELAY_MS 10u
#define QOTOM_PCIE_PENDING_BIT UINT32_C(0x00200000)

typedef int (*qotom_pcie_pending_delay)(void *,uint32_t);
struct qotom_pcie_pending_result { uint32_t polls,device_status; };
enum qotom_pcie_pending_status {
    QOTOM_PCIE_PENDING_OK,QOTOM_PCIE_PENDING_ARGUMENT,
    QOTOM_PCIE_PENDING_PRIOR,QOTOM_PCIE_PENDING_COMMAND,
    QOTOM_PCIE_PENDING_OBSERVATION,QOTOM_PCIE_PENDING_CHANGED,
    QOTOM_PCIE_PENDING_DELAY,QOTOM_PCIE_PENDING_TIMEOUT
};

static inline int qotom_pcie_pending_same_sample(
        const struct pci_express_observation *prior,
        const struct pci_express_observation *sample) {
    return prior && sample && sample->status==PCI_EXPRESS_OK &&
        prior->status==PCI_EXPRESS_OK && sample->offset==prior->offset &&
        sample->device_capabilities==prior->device_capabilities &&
        ((sample->device_control_status^prior->device_control_status)&
            ~QOTOM_PCIE_PENDING_BIT)==0;
}

/* BME and the device-specific stop checks precede this helper. Each poll
 * brackets the Device Capability and Device Control/Status reads with complete
 * identity/capability-list collections, and checks Command=0003 before and
 * after. Success requires two TP-clear Device Status samples separated by a
 * bounded 10-ms delay. At most 100 observations and 99 delays are attempted;
 * the first failed operation stops.
 *
 * PCIe Device Status.Transactions Pending describes outstanding non-posted
 * requests from this Function. Clear samples do not prove that posted writes
 * have reached memory, exclude firmware/AP activity, or establish whole-system
 * DMA containment. Callback serialization, timer continuity and device
 * obedience remain caller/profile obligations. */
static inline enum qotom_pcie_pending_status qotom_confirm_pcie_nonposted_quiet(
        pci_enumeration_read read,void *context,
        qotom_pcie_pending_delay delay,void *delay_context,
        const struct pci_enumeration_header *initial,
        const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *prior,
        struct qotom_pcie_pending_result *out) {
    if(out)*out=(struct qotom_pcie_pending_result){0};
    if(!read || !delay || !initial || !caps || !prior || !out ||
       prior->status!=PCI_EXPRESS_OK)return QOTOM_PCIE_PENDING_ARGUMENT;
    struct pci_enumeration_header current=*initial;
    current.words[1]=(current.words[1]&UINT32_C(0xffff0000))|3;
    unsigned clear=0;
    for(unsigned poll=0;poll<QOTOM_PCIE_PENDING_POLL_LIMIT;++poll) {
        uint32_t command;
        if(!read(context,current.bus,current.device,current.function,4,&command) ||
           (command&UINT32_C(0xffff))!=3)return QOTOM_PCIE_PENDING_COMMAND;
        struct pci_express_observation sample=
            pci_observe_express(read,context,&current,caps);
        if(sample.status!=PCI_EXPRESS_OK)return QOTOM_PCIE_PENDING_OBSERVATION;
        if(!qotom_pcie_pending_same_sample(prior,&sample))
            return QOTOM_PCIE_PENDING_CHANGED;
        if(!read(context,current.bus,current.device,current.function,4,&command) ||
           (command&UINT32_C(0xffff))!=3)return QOTOM_PCIE_PENDING_COMMAND;
        out->polls=poll+1;
        out->device_status=sample.device_control_status>>16;
        if(sample.device_control_status&QOTOM_PCIE_PENDING_BIT)clear=0;
        else if(++clear==2)return QOTOM_PCIE_PENDING_OK;
        if(poll+1==QOTOM_PCIE_PENDING_POLL_LIMIT)
            return QOTOM_PCIE_PENDING_TIMEOUT;
        if(!delay(delay_context,QOTOM_PCIE_PENDING_DELAY_MS))
            return QOTOM_PCIE_PENDING_DELAY;
    }
    return QOTOM_PCIE_PENDING_TIMEOUT;
}

static inline int qotom_rootport_pending_prior_valid(
        const struct pci_enumeration_header *header,
        const struct pci_express_observation *prior,
        enum qotom_rootport_bme_status status,
        const struct qotom_rootport_bme_result *bme) {
    return qotom_rootport_header_valid(header) &&
        qotom_rootport_sample_valid(prior) && status==QOTOM_ROOTPORT_OK && bme &&
        bme->attempted==1 && bme->before_command==7 && bme->after_command==3;
}

static inline enum qotom_pcie_pending_status qotom_confirm_rootport_nonposted_quiet(
        pci_enumeration_read read,void *context,
        qotom_pcie_pending_delay delay,void *delay_context,
        const struct pci_enumeration_header *header,
        const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *prior,
        enum qotom_rootport_bme_status status,
        const struct qotom_rootport_bme_result *bme,
        struct qotom_pcie_pending_result *out) {
    if(out)*out=(struct qotom_pcie_pending_result){0};
    if(!qotom_rootport_pending_prior_valid(header,prior,status,bme))
        return QOTOM_PCIE_PENDING_PRIOR;
    return qotom_confirm_pcie_nonposted_quiet(read,context,delay,delay_context,
        header,caps,prior,out);
}

static inline int qotom_realtek_pending_sample_valid(
        const struct pci_express_observation *sample) {
    return sample && sample->status==PCI_EXPRESS_OK && sample->offset==0x70 &&
        sample->device_capabilities==UINT32_C(0x05908cc0) &&
        !(sample->device_control_status&~UINT32_C(0x003f2000));
}

static inline int qotom_realtek_pending_prior_valid(
        const struct pci_enumeration_header *header,
        const struct pci_express_observation *pcie,
        enum qotom_realtek_status state_status,
        const struct qotom_realtek_state *state,
        enum qotom_realtek_bme_status bme_status,
        const struct qotom_realtek_bme_result *bme) {
    return qotom_realtek_header_valid(header) &&
        qotom_realtek_pending_sample_valid(pcie) &&
        state_status==QOTOM_REALTEK_OK && qotom_realtek_stopped(state) &&
        bme_status==QOTOM_REALTEK_BME_OK && bme && bme->attempted==1 &&
        bme->before_command==7 && bme->after_command==3;
}

static inline enum qotom_pcie_pending_status qotom_confirm_realtek_nonposted_quiet(
        pci_enumeration_read read,void *context,
        qotom_pcie_pending_delay delay,void *delay_context,
        const struct pci_enumeration_header *header,
        const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *pcie,
        enum qotom_realtek_status state_status,
        const struct qotom_realtek_state *state,
        enum qotom_realtek_bme_status bme_status,
        const struct qotom_realtek_bme_result *bme,
        struct qotom_pcie_pending_result *out) {
    if(out)*out=(struct qotom_pcie_pending_result){0};
    if(!qotom_realtek_pending_prior_valid(header,pcie,state_status,state,
            bme_status,bme))return QOTOM_PCIE_PENDING_PRIOR;
    return qotom_confirm_pcie_nonposted_quiet(read,context,delay,delay_context,
        header,caps,pcie,out);
}
#endif
