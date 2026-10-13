#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "qotom-broadcom-assign.h"
#include "boundary-abi.h"

/* The generated assignment variant (LeanOS/QotomBroadcomAssignment.lean)
 * linked from the same native object as the lab image. */
static unsigned cases;
static void expect(int condition,const char *what) {
    if(!condition) {
        fprintf(stderr,"Broadcom assignment boundary case %u: %s\n",cases,what);
        exit(1);
    }
    ++cases;
}
static uint64_t write_gate(const uint64_t a[13]) {
    return leanos_qotom_broadcom_assign_write(a[0],a[1],a[2],a[3],a[4],a[5],a[6],
        a[7],a[8],a[9],a[10],a[11],a[12]);
}
static uint64_t admission_gate(const uint64_t a[27]) {
    return leanos_qotom_broadcom_assign_admission(a[0],a[1],a[2],a[3],a[4],a[5],
        a[6],a[7],a[8],a[9],a[10],a[11],a[12],a[13],a[14],a[15],a[16],a[17],
        a[18],a[19],a[20],a[21],a[22],a[23],a[24],a[25],a[26]);
}

static uint32_t cfg[64];
static unsigned writes;
static int read_config(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    if(context!=cfg || bus!=2 || device || function || (offset&3))return 0;
    *value=cfg[offset/4];return 1;
}
static int write_word(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint16_t value) {
    if(context!=cfg || bus!=2 || device || function || offset!=0x44)return 0;
    ++writes;cfg[0x44/4]=(cfg[0x44/4]&UINT32_C(0xffff0000))|value;return 1;
}
static int wait_ms(void *context,uint32_t milliseconds) {
    return context==cfg && milliseconds==10;
}

int main(void) {
    (void)pci_enumerate_segment;
    const uint64_t write_ok[13]={1,0,6,0,0x4008,0x400b,0,0x400b,0xd0700004,0,0x44,2,0x4008};
    const uint64_t admission_ok[27]={1,0,6,0,0x4008,0x400b,0,0x400b,0xd0700004,0,
        0x44,2,0x4008,0,0x4008,0xd0700004,0,0x00190000,2,0x19,
        2,0,0,0x435314e4,0,UINT64_C(0x80100000000),2};
    expect(write_gate(write_ok)==1,"accepted store");
    expect(admission_gate(admission_ok)==1,"accepted assignment");
    /* Every single-bit mutation of every store input is refused. */
    for(unsigned i=0;i<13;++i)for(unsigned bit=0;bit<64;++bit) {
        uint64_t a[13];memcpy(a,write_ok,sizeof a);a[i]^=UINT64_C(1)<<bit;
        expect(write_gate(a)==0,"mutated store");
    }
    /* Every single-bit mutation of every assignment input is refused, except
       a quiet-poll count still within 2..100 and a narrower policy. */
    for(unsigned i=0;i<27;++i)for(unsigned bit=0;bit<64;++bit) {
        uint64_t a[27];memcpy(a,admission_ok,sizeof a);a[i]^=UINT64_C(1)<<bit;
        int narrower=(i==18 && a[18]>=2 && a[18]<=100) ||
            (i==25 && (bit==32 || bit==43)) || (i==26 && bit==1);
        expect(admission_gate(a)==(narrower?1u:0u),"mutated assignment");
    }
    /* The assignment variant consumes the initial contract's result for the
       retained final Command vector. */
    static const uint64_t commands[16]={7,3,3,2,0x102,2,3,3,3,3,0x402,7,3,3,0,3};
    uint64_t contract=leanos_qotom_pci_initial_trust_contract(commands[0],commands[1],
        commands[2],commands[3],commands[4],commands[5],commands[6],commands[7],
        commands[8],commands[9],commands[10],commands[11],commands[12],commands[13],
        commands[14],commands[15]);
    expect(contract==1,"initial trust contract");
    uint64_t bad_contract=leanos_qotom_pci_initial_trust_contract(commands[0],commands[1],
        commands[2],commands[3],commands[4],commands[5],commands[6],commands[7],
        commands[8],commands[9],commands[10],commands[11],commands[12],commands[13],
        6,commands[15]);
    expect(bad_contract==0,"Broadcom Command 0006 in the final vector");

    /* The native sequence with the generated gates. */
    struct pci_enumeration_header endpoint={.bus=2,.words={
        0x435314e4,0x00100006,0x02800001,0x10,0xd0700004,0,0,0,
        0,0,0,0x04d814e4,0,0x40,0,0x105}};
    struct pci_capability_snapshot caps={.count=4,.headers={
        {0x40,0xce035801},{0x58,0x00784809},{0x48,0x0080d005},{0xd0,0x00010010}}};
    struct pci_express_observation prior={PCI_EXPRESS_OK,0xd0,0x05908fa0,0x00190000};
    struct qotom_broadcom_d3_result d3={1,6,0,2,0x19,0x4008,1,0x400b};
    struct qotom_broadcom_assign_policy policy={2,0,0,0x435314e4,0,
        UINT64_C(0x80100000000),2};
    for(unsigned variant=0;variant<4;++variant) {
        memset(cfg,0,sizeof cfg);memcpy(cfg,endpoint.words,sizeof endpoint.words);
        cfg[1]=UINT32_C(0x00100000);cfg[0x40/4]=UINT32_C(0xce035801);
        cfg[0x44/4]=UINT32_C(0x400b);cfg[0x58/4]=UINT32_C(0x00784809);
        cfg[0x48/4]=UINT32_C(0x0080d005);cfg[0xd0/4]=UINT32_C(0x00010010);
        cfg[0xd4/4]=UINT32_C(0x05908fa0);cfg[0xd8/4]=UINT32_C(0x00190000);
        writes=0;
        struct qotom_broadcom_assign_policy offered=policy;
        if(variant==3)offered.cmd_set=6;
        if(variant==2)cfg[0x44/4]=UINT32_C(0x4008);
        struct qotom_broadcom_assign_result out;
        enum qotom_broadcom_assign_status s=qotom_broadcom_assign_d0(read_config,cfg,
            write_word,cfg,wait_ms,cfg,&endpoint,&caps,&prior,QOTOM_BROADCOM_D3_OK,&d3,
            variant==1?bad_contract:contract,&offered,
            leanos_qotom_broadcom_assign_write,leanos_qotom_broadcom_assign_admission,&out);
        if(variant==0)expect(s==QOTOM_BROADCOM_ASSIGN_OK && out.admitted==1 && writes==1 &&
            (cfg[0x44/4]&0xffff)==0x4008,"generated sequence admits");
        else if(variant==3)expect(s==QOTOM_BROADCOM_ASSIGN_GENERATED_ADMISSION &&
            !out.admitted && writes==1,"bus-master policy refused");
        else expect(s==QOTOM_BROADCOM_ASSIGN_GENERATED_WRITE && !writes,
            variant==1?"contract refused before the store":"D0 device refused before the store");
    }
    printf("PASS Qotom Broadcom assignment boundary: %u cases\n",cases);
    return 0;
}
