#ifndef LEANOS_QOTOM_PCI_FINAL_ADMISSION_H
#define LEANOS_QOTOM_PCI_FINAL_ADMISSION_H
#include "qotom-native-inventory.h"

typedef uint64_t (*qotom_pci_final_commands_check)(
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t);
typedef uint64_t (*qotom_pci_final_admission_check)(
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,
    uint64_t,uint64_t,uint64_t,uint64_t,uint64_t);

struct qotom_pci_final_assumptions {
    uint64_t fixed_infrastructure_noninitiating;
    uint64_t lpc_no_dma;
    uint64_t posted_writes_drained;
    uint64_t txe_private_dma_quiescent;
    uint64_t firmware_and_smm_noninterference;
};

enum qotom_pci_final_status {
    QOTOM_PCI_FINAL_MATCH,
    QOTOM_PCI_FINAL_ARGUMENT,
    QOTOM_PCI_FINAL_SCAN,
    QOTOM_PCI_FINAL_COUNT,
    QOTOM_PCI_FINAL_HEADER,
    QOTOM_PCI_FINAL_COMMAND,
    QOTOM_PCI_FINAL_ASSUMPTIONS,
    QOTOM_PCI_FINAL_GENERATED
};

struct qotom_pci_final_result {
    enum qotom_pci_final_status status;
    uint32_t index;
    uint32_t assumption_mask;
    uint32_t commands_accepted;
    uint32_t admitted;
    uint16_t commands[16];
};

/* This is a final observation and conditional-admission boundary. It performs
 * no PCI or MMIO access and grants no authority. The caller must supply a
 * fresh, complete post-transition snapshot plus the generated Lean checks.
 * Assumptions are reported independently from observed identity and Command
 * words; zero-valued unestablished assumptions cannot produce admission. */
static inline struct qotom_pci_final_result qotom_check_pci_final(
        enum pci_enumeration_status scan_status,
        const struct pci_enumeration_snapshot *snapshot,
        qotom_native_header_check header_check,
        qotom_pci_final_commands_check commands_check,
        qotom_pci_final_admission_check admission_check,
        const struct qotom_pci_final_assumptions *assumptions) {
    struct qotom_pci_final_result out={QOTOM_PCI_FINAL_ARGUMENT,0,0,0,0,{0}};
    if(!snapshot || !header_check || !commands_check || !admission_check || !assumptions)
        return out;
    if(scan_status!=PCI_ENUMERATION_OK) { out.status=QOTOM_PCI_FINAL_SCAN;return out; }
    if(snapshot->count!=16) { out.status=QOTOM_PCI_FINAL_COUNT;return out; }
    for(uint32_t i=0;i<16;++i) {
        const struct pci_enumeration_header *h=&snapshot->headers[i];
        const uint32_t *w=h->words;
        out.index=i;
        if(header_check(i,h->bus,h->device,h->function,w[0],w[1],w[2],w[3],
                w[4],w[5],w[6],w[7],w[8],w[9],w[10],w[11],w[12],w[13],w[14],w[15])!=1) {
            out.status=QOTOM_PCI_FINAL_HEADER;return out;
        }
        out.commands[i]=(uint16_t)w[1];
    }
    out.commands_accepted=(uint32_t)commands_check(
        out.commands[0],out.commands[1],out.commands[2],out.commands[3],
        out.commands[4],out.commands[5],out.commands[6],out.commands[7],
        out.commands[8],out.commands[9],out.commands[10],out.commands[11],
        out.commands[12],out.commands[13],out.commands[14],out.commands[15]);
    if(out.commands_accepted!=1) { out.status=QOTOM_PCI_FINAL_COMMAND;return out; }
    out.index=16;
    const uint64_t values[5]={assumptions->fixed_infrastructure_noninitiating,
        assumptions->lpc_no_dma,assumptions->posted_writes_drained,
        assumptions->txe_private_dma_quiescent,
        assumptions->firmware_and_smm_noninterference};
    for(uint32_t i=0;i<5;++i)if(values[i]==1)out.assumption_mask|=1u<<i;
    out.admitted=(uint32_t)admission_check(
        out.commands[0],out.commands[1],out.commands[2],out.commands[3],
        out.commands[4],out.commands[5],out.commands[6],out.commands[7],
        out.commands[8],out.commands[9],out.commands[10],out.commands[11],
        out.commands[12],out.commands[13],out.commands[14],out.commands[15],
        values[0],values[1],values[2],values[3],values[4]);
    if(out.assumption_mask!=0x1f) { out.status=QOTOM_PCI_FINAL_ASSUMPTIONS;return out; }
    if(out.admitted!=1) { out.status=QOTOM_PCI_FINAL_GENERATED;return out; }
    out.status=QOTOM_PCI_FINAL_MATCH;out.index=16;return out;
}
#endif
