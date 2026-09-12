#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "qotom-pci-final-admission.h"
#include "boundary-abi.h"
#include "capture.h"

static unsigned cases;
static void expect(enum qotom_pci_final_status actual,
        enum qotom_pci_final_status wanted) {
    if(actual!=wanted) {
        fprintf(stderr,"final PCI case %u: %u != %u\n",cases,actual,wanted);
        exit(1);
    }
    ++cases;
}
static uint64_t reject_commands(
    uint64_t a0,uint64_t a1,uint64_t a2,uint64_t a3,uint64_t a4,uint64_t a5,
    uint64_t a6,uint64_t a7,uint64_t a8,uint64_t a9,uint64_t a10,uint64_t a11,
    uint64_t a12,uint64_t a13,uint64_t a14,uint64_t a15) {
    (void)a0;(void)a1;(void)a2;(void)a3;(void)a4;(void)a5;(void)a6;(void)a7;
    (void)a8;(void)a9;(void)a10;(void)a11;(void)a12;(void)a13;(void)a14;(void)a15;
    return 0;
}
static uint64_t reject_admission(
    uint64_t a0,uint64_t a1,uint64_t a2,uint64_t a3,uint64_t a4,uint64_t a5,
    uint64_t a6,uint64_t a7,uint64_t a8,uint64_t a9,uint64_t a10,uint64_t a11,
    uint64_t a12,uint64_t a13,uint64_t a14,uint64_t a15,uint64_t a16,
    uint64_t a17,uint64_t a18,uint64_t a19,uint64_t a20) {
    (void)a0;(void)a1;(void)a2;(void)a3;(void)a4;(void)a5;(void)a6;(void)a7;
    (void)a8;(void)a9;(void)a10;(void)a11;(void)a12;(void)a13;(void)a14;(void)a15;
    (void)a16;(void)a17;(void)a18;(void)a19;(void)a20;return 0;
}
static struct qotom_pci_final_result check(
        const struct pci_enumeration_snapshot *snapshot,
        const struct qotom_pci_final_assumptions *assumptions) {
    return qotom_check_pci_final(PCI_ENUMERATION_OK,snapshot,
        leanos_qotom_native_pci_header_check,leanos_qotom_pci_final_commands,
        leanos_qotom_pci_final_admission,assumptions);
}
int main(void) {
    static const uint16_t commands[16]={7,3,3,2,0x102,2,3,3,3,3,0x402,7,3,3,0,3};
    struct pci_enumeration_snapshot input=captured;
    for(unsigned i=0;i<16;++i)
        input.headers[i].words[1]=(input.headers[i].words[1]&UINT32_C(0xffff0000))|commands[i];
    const struct pci_enumeration_snapshot final=input;
    struct qotom_pci_final_assumptions all={1,1,1,1,1};
    struct qotom_pci_final_assumptions none={0,0,0,0,0};
    struct qotom_pci_final_result result=check(&input,&all);
    expect(result.status,QOTOM_PCI_FINAL_MATCH);
    if(result.index!=16 || result.assumption_mask!=0x1f ||
       result.commands_accepted!=1 || result.admitted!=1 ||
       memcmp(result.commands,commands,sizeof commands) ||
       memcmp(&input,&final,sizeof input))return 2;
    expect(check(&input,&none).status,QOTOM_PCI_FINAL_ASSUMPTIONS);
    expect(qotom_check_pci_final(PCI_ENUMERATION_OK,NULL,
        leanos_qotom_native_pci_header_check,leanos_qotom_pci_final_commands,
        leanos_qotom_pci_final_admission,&all).status,QOTOM_PCI_FINAL_ARGUMENT);
    expect(qotom_check_pci_final(PCI_ENUMERATION_READ_FAILED,&input,
        leanos_qotom_native_pci_header_check,leanos_qotom_pci_final_commands,
        leanos_qotom_pci_final_admission,&all).status,QOTOM_PCI_FINAL_SCAN);
    input.count=15;expect(check(&input,&all).status,QOTOM_PCI_FINAL_COUNT);
    input=final;input.headers[8].words[0]^=1;
    result=check(&input,&all);expect(result.status,QOTOM_PCI_FINAL_HEADER);
    if(result.index!=8)return 3;
    for(unsigned i=0;i<16;++i) {
        input=final;input.headers[i].words[1]^=1;
        expect(check(&input,&all).status,QOTOM_PCI_FINAL_COMMAND);
    }
    for(unsigned i=0;i<5;++i) {
        struct qotom_pci_final_assumptions one_missing=all;
        uint64_t *values[5]={&one_missing.fixed_infrastructure_noninitiating,
            &one_missing.lpc_no_dma,&one_missing.posted_writes_drained,
            &one_missing.txe_private_dma_quiescent,
            &one_missing.firmware_and_smm_noninterference};
        *values[i]=0;
        result=check(&final,&one_missing);
        expect(result.status,QOTOM_PCI_FINAL_ASSUMPTIONS);
        if(result.admitted || result.assumption_mask!=(0x1fu^(1u<<i)))return 4;
    }
    result=qotom_check_pci_final(PCI_ENUMERATION_OK,&final,
        leanos_qotom_native_pci_header_check,reject_commands,
        leanos_qotom_pci_final_admission,&all);
    expect(result.status,QOTOM_PCI_FINAL_COMMAND);
    result=qotom_check_pci_final(PCI_ENUMERATION_OK,&final,
        leanos_qotom_native_pci_header_check,leanos_qotom_pci_final_commands,
        reject_admission,&all);
    expect(result.status,QOTOM_PCI_FINAL_GENERATED);
    printf("PASS Qotom final PCI boundary: %u cases\n",cases);
    return 0;
}
