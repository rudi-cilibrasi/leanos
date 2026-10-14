#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-broadcom-assign.h"

static uint32_t cfg[64];
static struct pci_enumeration_header endpoint;
static struct pci_capability_snapshot caps;
static struct pci_express_observation prior;
static struct qotom_broadcom_d3_result d3;
static enum qotom_broadcom_d3_status d3_status;
static struct qotom_broadcom_assign_policy policy;
static unsigned reads,writes,delays,fail_read,fail_write,fail_delay,pending_polls;
static unsigned stay_d3,write_checks,admission_checks;
static uint64_t write_args[13],admission_args[27],write_answer,admission_answer;
static const uint64_t want_write[13]={1,0,6,0,0x4008,0x400b,0,0x400b,0xd0700004,0,0x44,2,0x4008};
static const uint64_t want_admission[27]={1,0,6,0,0x4008,0x400b,0,0x400b,0xd0700004,0,
    0x44,2,0x4008,0,0x4008,0xd0700004,0,0x00190000,2,0x19,
    2,0,0,0x435314e4,0,UINT64_C(0x80100000000),2};

static int read_config(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    assert(context==cfg && bus==2 && !device && !function && !(offset&3));
    ++reads;if(reads==fail_read)return 0;
    *value=cfg[offset/4];
    if(offset==0xd8 && writes && delays>1 && delays-1<pending_polls)
        *value|=QOTOM_PCIE_PENDING_BIT;
    return 1;
}
static int write_word(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint16_t value) {
    assert(context==cfg && bus==2 && !device && !function);
    ++writes;assert(writes==1 && offset==0x44 && value==QOTOM_BROADCOM_PMCSR_D0);
    assert(write_checks==1 && !delays);
    if(writes==fail_write)return 0;
    if(!stay_d3)cfg[0x44/4]=(cfg[0x44/4]&UINT32_C(0xffff0000))|value;
    return 1;
}
static int wait10(void *context,uint32_t milliseconds) {
    assert(context==(void *)0x1234 && milliseconds==10 && writes==1);
    ++delays;return delays!=fail_delay;
}
static uint64_t write_check(uint64_t a0,uint64_t a1,uint64_t a2,uint64_t a3,
        uint64_t a4,uint64_t a5,uint64_t a6,uint64_t a7,uint64_t a8,uint64_t a9,
        uint64_t a10,uint64_t a11,uint64_t a12) {
    const uint64_t a[13]={a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12};
    memcpy(write_args,a,sizeof a);++write_checks;assert(!writes);
    return memcmp(a,want_write,sizeof a)?0:write_answer;
}
static uint64_t admission_check(uint64_t a0,uint64_t a1,uint64_t a2,uint64_t a3,
        uint64_t a4,uint64_t a5,uint64_t a6,uint64_t a7,uint64_t a8,uint64_t a9,
        uint64_t a10,uint64_t a11,uint64_t a12,uint64_t a13,uint64_t a14,
        uint64_t a15,uint64_t a16,uint64_t a17,uint64_t a18,uint64_t a19,
        uint64_t a20,uint64_t a21,uint64_t a22,uint64_t a23,uint64_t a24,
        uint64_t a25,uint64_t a26) {
    const uint64_t a[27]={a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,
        a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26};
    memcpy(admission_args,a,sizeof a);++admission_checks;
    return memcmp(a,want_admission,sizeof a)?0:admission_answer;
}
static void setup(void) {
    memset(cfg,0,sizeof cfg);memset(&endpoint,0,sizeof endpoint);
    const uint32_t words[16]={0x435314e4,0x00100006,0x02800001,0x10,
        0xd0700004,0,0,0,0,0,0,0x04d814e4,0,0x40,0,0x105};
    endpoint.bus=2;memcpy(endpoint.words,words,sizeof words);memcpy(cfg,words,sizeof words);
    cfg[0x40/4]=UINT32_C(0xce035801);cfg[0x44/4]=UINT32_C(0x00004008);
    cfg[0x58/4]=UINT32_C(0x00784809);cfg[0x48/4]=UINT32_C(0x0080d005);
    cfg[0xd0/4]=UINT32_C(0x00010010);cfg[0xd4/4]=UINT32_C(0x05908fa0);
    cfg[0xd8/4]=UINT32_C(0x00190000);
    reads=0;fail_read=0;writes=0;
    assert(pci_collect_capabilities(read_config,cfg,&endpoint,&caps).status==PCI_CAPABILITY_OK);
    prior=pci_observe_express(read_config,cfg,&endpoint,&caps);
    assert(qotom_broadcom_pcie_valid(&prior));
    /* The state the D3hot transition left: Command 0000, PMCSR 400b. */
    cfg[1]=UINT32_C(0x00100000);cfg[0x44/4]=UINT32_C(0x0000400b);
    d3=(struct qotom_broadcom_d3_result){1,6,0,2,0x19,0x4008,1,0x400b};
    d3_status=QOTOM_BROADCOM_D3_OK;
    policy=(struct qotom_broadcom_assign_policy){2,0,0,0x435314e4,0,
        UINT64_C(0x80100000000),2};
    reads=writes=delays=fail_read=fail_write=fail_delay=pending_polls=0;
    stay_d3=write_checks=admission_checks=0;write_answer=admission_answer=1;
    memset(write_args,0xee,sizeof write_args);memset(admission_args,0xee,sizeof admission_args);
}
static enum qotom_broadcom_assign_status run(struct qotom_broadcom_assign_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_broadcom_assign_d0(read_config,cfg,write_word,cfg,wait10,(void *)0x1234,
        &endpoint,&caps,&prior,d3_status,&d3,1,&policy,write_check,admission_check,out);
}
int main(void) {
    (void)pci_enumerate_segment;
    struct qotom_broadcom_assign_result out;
    setup();assert(run(&out)==QOTOM_BROADCOM_ASSIGN_OK);
    const unsigned total=reads;
    assert(writes==1 && delays==2 && write_checks==1 && admission_checks==1);
    assert(out.pre_command==0 && out.pre_pmcsr==0x400b && out.pre_bar0==0xd0700004 &&
        !out.pre_bar1 && out.write_accepted==1 && out.d0_attempted==1 &&
        out.after_pmcsr==0x4008 && !out.post_command && out.post_bar0==0xd0700004 &&
        !out.post_bar1 && out.device_control_status==0x00190000 &&
        out.pending_polls==2 && out.device_status==0x19 && out.admitted==1);
    assert(!memcmp(write_args,want_write,sizeof want_write));
    assert(!memcmp(admission_args,want_admission,sizeof want_admission));
    /* Every read failure stops the sequence; none before the store writes. */
    for(unsigned n=1;n<=total;++n) {
        setup();fail_read=n;enum qotom_broadcom_assign_status s=run(&out);
        assert(s!=QOTOM_BROADCOM_ASSIGN_OK && reads==n && writes<=1 && !out.admitted);
        if(s==QOTOM_BROADCOM_ASSIGN_PRE)assert(!writes && !write_checks);
    }
    setup();fail_write=1;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PM_WRITE && !delays &&
        out.d0_attempted && !admission_checks);
    setup();fail_delay=1;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_DELAY && !admission_checks);
    setup();fail_delay=2;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PENDING && !admission_checks);
    /* The generated checks decide: a refusal before the store writes nothing. */
    setup();write_answer=0;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_GENERATED_WRITE &&
        !writes && !out.d0_attempted);
    setup();write_answer=2;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_GENERATED_WRITE && !writes);
    setup();admission_answer=0;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_GENERATED_ADMISSION &&
        writes==1 && !out.admitted);
    /* A device that stays in D3hot, a header change after D0, or pending
       transactions that never clear are post-transition rejections. */
    setup();stay_d3=1;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_POST && !admission_checks);
    setup();pending_polls=100;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PENDING &&
        out.pending_polls==100 && !admission_checks);
    setup();pending_polls=3;assert(run(&out)==QOTOM_BROADCOM_ASSIGN_GENERATED_ADMISSION &&
        out.pending_polls==5);
    /* Every bit of the configuration space the sequence reads. */
    for(unsigned word=0;word<64;++word)for(unsigned bit=0;bit<32;++bit) {
        setup();cfg[word]^=UINT32_C(1)<<bit;
        enum qotom_broadcom_assign_status s=run(&out);
        if(word==1 && bit>=16 && bit!=20)assert(s==QOTOM_BROADCOM_ASSIGN_OK);
        else if(word<16 || word==0x40/4 || word==0x58/4 || word==0x48/4 || word==0xd0/4)
            assert(s==QOTOM_BROADCOM_ASSIGN_PRE && !writes && !write_checks);
        else if(word==0x44/4 && bit<16)
            assert(s==QOTOM_BROADCOM_ASSIGN_GENERATED_WRITE && !writes);
        else if(word==0x44/4)assert(s==QOTOM_BROADCOM_ASSIGN_POST && writes==1);
        else if(word==0xd4/4 || word==0xd8/4)
            assert(s==QOTOM_BROADCOM_ASSIGN_POST && writes==1 && !admission_checks);
        else assert(s==QOTOM_BROADCOM_ASSIGN_OK);
    }
    /* Every bit of the offered policy reaches only the generated check. */
    for(unsigned field=0;field<7;++field)for(unsigned bit=0;bit<64;++bit) {
        setup();((uint64_t *)&policy)[field]^=UINT64_C(1)<<bit;
        assert(run(&out)==QOTOM_BROADCOM_ASSIGN_GENERATED_ADMISSION && !out.admitted);
    }
    /* Every bit of every prior is rejected before any configuration access. */
    for(unsigned field=0;field<8;++field)for(unsigned bit=0;bit<32;++bit) {
        setup();((uint32_t *)&d3)[field]^=UINT32_C(1)<<bit;
        int accepted=field==3 && d3.pending_polls>=2 && d3.pending_polls<=100;
        if(accepted){assert(run(&out)==QOTOM_BROADCOM_ASSIGN_OK);continue;}
        assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PRIOR && !reads && !writes);
    }
    for(unsigned status=1;status<=13;++status) {
        setup();d3_status=(enum qotom_broadcom_d3_status)status;
        assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PRIOR && !reads && !writes);
    }
    for(unsigned word=0;word<16;++word)for(unsigned bit=0;bit<32;++bit) {
        setup();endpoint.words[word]^=UINT32_C(1)<<bit;
        int relevant=word==0 || word==2 || word==4 || word==5 || word==11 || word==13 ||
            (word==1 && bit<16) || (word==3 && bit>=16 && bit<24);
        enum qotom_broadcom_assign_status s=run(&out);
        if(relevant)assert(s==QOTOM_BROADCOM_ASSIGN_PRIOR && !reads && !writes);
        else if(word==1 && bit!=20)assert(s==QOTOM_BROADCOM_ASSIGN_OK);
        else assert(s==QOTOM_BROADCOM_ASSIGN_PRE && !writes);
    }
    for(unsigned i=0;i<4;++i)for(unsigned bit=0;bit<32;++bit) {
        setup();caps.headers[i].raw^=UINT32_C(1)<<bit;
        assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PRIOR && !reads && !writes);
    }
    for(unsigned bit=0;bit<32;++bit) {
        setup();prior.device_capabilities^=UINT32_C(1)<<bit;
        assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PRIOR && !reads);
        setup();prior.device_control_status^=UINT32_C(1)<<bit;
        assert(run(&out)==QOTOM_BROADCOM_ASSIGN_PRIOR && !reads);
    }
    setup();memset(&out,0xff,sizeof out);
    assert(qotom_broadcom_assign_d0(read_config,cfg,write_word,cfg,wait10,(void *)0x1234,
        &endpoint,&caps,&prior,d3_status,&d3,1,&policy,NULL,admission_check,&out)==
        QOTOM_BROADCOM_ASSIGN_ARGUMENT && !out.d0_attempted && !reads);
    assert(qotom_broadcom_assign_d0(read_config,cfg,write_word,cfg,wait10,(void *)0x1234,
        &endpoint,&caps,&prior,d3_status,NULL,1,&policy,write_check,admission_check,&out)==
        QOTOM_BROADCOM_ASSIGN_ARGUMENT && !reads);
    printf("PASS Broadcom assign: one PMCSR store, D0 recovery, header/PCIe/quiet checks, generated gates, %u read failures\n",total);
}
