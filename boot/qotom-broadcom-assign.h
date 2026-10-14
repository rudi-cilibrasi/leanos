#ifndef LEANOS_QOTOM_BROADCOM_ASSIGN_H
#define LEANOS_QOTOM_BROADCOM_ASSIGN_H
#include "qotom-broadcom-d3.h"

/* Reviewed assignment variant qotom-j1900-pci-trust-v1-bcm43224-assign-v1
 * (docs/adr/0027-qotom-broadcom-assignment-contract.md). The Lean module
 * LeanOS/QotomBroadcomAssignment.lean decides the variant; this header only
 * sequences configuration accesses and hands every observation to the two
 * generated checks. */
#define QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET 0x44u
#define QOTOM_BROADCOM_ASSIGN_WIDTH 2u
#define QOTOM_BROADCOM_ASSIGN_RECOVERY_MS 10u
#define QOTOM_BROADCOM_BAR0 UINT32_C(0xd0700004)

typedef uint64_t (*qotom_broadcom_assign_write_check)(
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t);
typedef uint64_t (*qotom_broadcom_assign_admission_check)(
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,
    uint64_t,uint64_t,uint64_t);

/* The program policy offered for assignment, in the image header's terms. */
struct qotom_broadcom_assign_policy {
    uint64_t bus,device,function,identity,dma,cfg_write,cmd_set;
};
struct qotom_broadcom_assign_result {
    uint32_t pre_command,pre_pmcsr,pre_bar0,pre_bar1;
    uint32_t write_accepted,d0_attempted,after_pmcsr;
    uint32_t post_command,post_bar0,post_bar1,device_control_status;
    uint32_t pending_polls,device_status,admitted;
};
enum qotom_broadcom_assign_status {
    QOTOM_BROADCOM_ASSIGN_OK,QOTOM_BROADCOM_ASSIGN_ARGUMENT,
    QOTOM_BROADCOM_ASSIGN_PRIOR,QOTOM_BROADCOM_ASSIGN_PRE,
    QOTOM_BROADCOM_ASSIGN_GENERATED_WRITE,QOTOM_BROADCOM_ASSIGN_PM_WRITE,
    QOTOM_BROADCOM_ASSIGN_DELAY,QOTOM_BROADCOM_ASSIGN_POST,
    QOTOM_BROADCOM_ASSIGN_PENDING,QOTOM_BROADCOM_ASSIGN_FINAL,
    QOTOM_BROADCOM_ASSIGN_GENERATED_ADMISSION
};

/* The retained D3hot record must be the exact successful one. */
static inline int qotom_broadcom_assign_d3_valid(enum qotom_broadcom_d3_status status,
        const struct qotom_broadcom_d3_result *d3) {
    return status==QOTOM_BROADCOM_D3_OK && d3 && d3->command_attempted==1 &&
        d3->before_command==QOTOM_BROADCOM_COMMAND_INITIAL &&
        d3->after_command==QOTOM_BROADCOM_COMMAND_DISABLED &&
        d3->pending_polls>=2 && d3->pending_polls<=QOTOM_PCIE_PENDING_POLL_LIMIT &&
        d3->device_status==0x19 && d3->before_pmcsr==QOTOM_BROADCOM_PMCSR_D0 &&
        d3->d3_attempted==1 && d3->after_pmcsr==QOTOM_BROADCOM_PMCSR_D3HOT;
}

/* The complete header must equal the retained inventory header with Command
 * replaced; Status may change only outside its Capabilities List bit. The
 * capability list must be the retained four entries. */
static inline int qotom_broadcom_assign_header(pci_enumeration_read read,void *context,
        const struct pci_enumeration_header *initial,
        const struct pci_capability_snapshot *caps,uint16_t command,
        struct pci_enumeration_header *current) {
    *current=*initial;
    current->words[1]=(current->words[1]&UINT32_C(0xffff0000))|command;
    for(unsigned i=0;i<16;++i) {
        uint32_t raw,mask=i==1?UINT32_C(0x0010ffff):UINT32_MAX;
        if(!read(context,2,0,0,(uint8_t)(i*4),&raw) ||
           (raw&mask)!=(current->words[i]&mask))return 0;
    }
    struct pci_capability_snapshot list;
    return pci_collect_capabilities(read,context,current,&list).status==PCI_CAPABILITY_OK &&
        qotom_broadcom_same_list(caps,&list);
}

static inline uint64_t qotom_broadcom_assign_write_query(
        qotom_broadcom_assign_write_check check,uint64_t contract,
        enum qotom_broadcom_d3_status d3_status,const struct qotom_broadcom_d3_result *d3,
        const struct qotom_broadcom_assign_result *out) {
    return check(contract,(uint64_t)d3_status,d3->before_command,d3->after_command,
        d3->before_pmcsr,d3->after_pmcsr,out->pre_command,out->pre_pmcsr,
        out->pre_bar0,out->pre_bar1,QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET,
        QOTOM_BROADCOM_ASSIGN_WIDTH,QOTOM_BROADCOM_PMCSR_D0);
}

/* D3hot -> D0 for the assigned BCM43224 at 02:00.0.
 *
 * Preconditions bound before any access: the exact retained inventory
 * header (Command 0006), capability list and PCIe observation, and the exact
 * successful D3hot record of this boot. `contract` is the generated
 * qotom-j1900-pci-trust-v1 result for the retained final Command vector.
 *
 * 1. Re-read the complete header (Command 0000, unchanged BARs) and the
 *    capability list, then PMCSR, which must still be 400b (D3hot).
 * 2. The generated write check must permit the one store; otherwise nothing
 *    is written.
 * 3. One 16-bit store of 4008 to PMCSR (offset 44): PowerState D0, PME
 *    disabled, every other field as read. No other configuration write.
 * 4. Wait the PCI PM 1.2 D3hot -> D0 recovery time of 10 ms before the next
 *    configuration access.
 * 5. Refresh the complete header, capability list, PCIe Device
 *    Capability/Control/Status (retained 05908fa0/00190000, so Transactions
 *    Pending clear) and PMCSR 4008.
 * 6. Two Transactions-Pending-clear samples 10 ms apart with Command 0000.
 * 7. Read Command, BAR0, BAR1 and PMCSR once more and pass every
 *    observation and the program policy to the generated admission check.
 *
 * Success grants nothing by itself: the caller binds the program only on
 * status 0. A failed store may have taken effect; no rollback to D3hot is
 * attempted and the caller must fail closed. */
static inline enum qotom_broadcom_assign_status qotom_broadcom_assign_d0(
        pci_enumeration_read read,void *context,
        qotom_broadcom_write_word write,void *writer,
        qotom_pcie_pending_delay delay,void *delay_context,
        const struct pci_enumeration_header *endpoint,
        const struct pci_capability_snapshot *caps,
        const struct pci_express_observation *prior_pcie,
        enum qotom_broadcom_d3_status d3_status,
        const struct qotom_broadcom_d3_result *d3,
        uint64_t contract,
        const struct qotom_broadcom_assign_policy *policy,
        qotom_broadcom_assign_write_check write_check,
        qotom_broadcom_assign_admission_check admission_check,
        struct qotom_broadcom_assign_result *out) {
    if(out)*out=(struct qotom_broadcom_assign_result){0};
    if(!read || !write || !delay || !endpoint || !caps || !prior_pcie || !d3 ||
       !policy || !write_check || !admission_check || !out)
        return QOTOM_BROADCOM_ASSIGN_ARGUMENT;
    if(!qotom_broadcom_header_valid_command(endpoint,QOTOM_BROADCOM_COMMAND_INITIAL) ||
       endpoint->words[4]!=QOTOM_BROADCOM_BAR0 || endpoint->words[5] ||
       !qotom_broadcom_caps_valid(caps) || !qotom_broadcom_pcie_valid(prior_pcie) ||
       !qotom_broadcom_assign_d3_valid(d3_status,d3))
        return QOTOM_BROADCOM_ASSIGN_PRIOR;
    struct pci_enumeration_header current;
    uint32_t value;
    if(!qotom_broadcom_assign_header(read,context,endpoint,caps,
            QOTOM_BROADCOM_COMMAND_DISABLED,&current) ||
       !read(context,2,0,0,4,&value))return QOTOM_BROADCOM_ASSIGN_PRE;
    out->pre_command=value&0xffff;
    if(!read(context,2,0,0,0x10,&out->pre_bar0) ||
       !read(context,2,0,0,0x14,&out->pre_bar1) ||
       !read(context,2,0,0,QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET,&value))
        return QOTOM_BROADCOM_ASSIGN_PRE;
    out->pre_pmcsr=value&0xffff;
    if(qotom_broadcom_assign_write_query(write_check,contract,d3_status,d3,out)!=1)
        return QOTOM_BROADCOM_ASSIGN_GENERATED_WRITE;
    out->write_accepted=1;out->d0_attempted=1;
    if(!write(writer,2,0,0,QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET,QOTOM_BROADCOM_PMCSR_D0))
        return QOTOM_BROADCOM_ASSIGN_PM_WRITE;
    if(!delay(delay_context,QOTOM_BROADCOM_ASSIGN_RECOVERY_MS))
        return QOTOM_BROADCOM_ASSIGN_DELAY;
    struct pci_express_observation pcie;
    struct pci_power_observation power;
    if(!qotom_broadcom_assign_header(read,context,endpoint,caps,
            QOTOM_BROADCOM_COMMAND_DISABLED,&current) ||
       !qotom_broadcom_refresh(read,context,endpoint,caps,QOTOM_BROADCOM_COMMAND_DISABLED,
            QOTOM_BROADCOM_PMCSR_D0,&pcie,&power))return QOTOM_BROADCOM_ASSIGN_POST;
    out->after_pmcsr=power.control_status&0xffff;
    out->device_control_status=pcie.device_control_status;
    struct qotom_pcie_pending_result pending={0};
    enum qotom_pcie_pending_status ps=qotom_confirm_pcie_nonposted_quiet_command(
        read,context,delay,delay_context,endpoint,caps,prior_pcie,
        QOTOM_BROADCOM_COMMAND_DISABLED,&pending);
    out->pending_polls=pending.polls;out->device_status=pending.device_status;
    if(ps!=QOTOM_PCIE_PENDING_OK)return QOTOM_BROADCOM_ASSIGN_PENDING;
    if(!read(context,2,0,0,4,&value))return QOTOM_BROADCOM_ASSIGN_FINAL;
    out->post_command=value&0xffff;
    if(!read(context,2,0,0,0x10,&out->post_bar0) ||
       !read(context,2,0,0,0x14,&out->post_bar1) ||
       !read(context,2,0,0,QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET,&value))
        return QOTOM_BROADCOM_ASSIGN_FINAL;
    out->after_pmcsr=value&0xffff;
    if(admission_check(contract,(uint64_t)d3_status,d3->before_command,d3->after_command,
            d3->before_pmcsr,d3->after_pmcsr,out->pre_command,out->pre_pmcsr,
            out->pre_bar0,out->pre_bar1,QOTOM_BROADCOM_ASSIGN_PMCSR_OFFSET,
            QOTOM_BROADCOM_ASSIGN_WIDTH,QOTOM_BROADCOM_PMCSR_D0,
            out->post_command,out->after_pmcsr,out->post_bar0,out->post_bar1,
            out->device_control_status,out->pending_polls,out->device_status,
            policy->bus,policy->device,policy->function,policy->identity,
            policy->dma,policy->cfg_write,policy->cmd_set)!=1)
        return QOTOM_BROADCOM_ASSIGN_GENERATED_ADMISSION;
    out->admitted=1;return QOTOM_BROADCOM_ASSIGN_OK;
}
#endif
