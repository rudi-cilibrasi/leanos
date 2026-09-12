#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-xhci-handoff.h"
static const struct pci_enumeration_header initial={.device=20,.words={0x0f358086,6,0x0c03300e,0,0xd0900004,0}};
static const struct qotom_xhci_capabilities caps={{0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000}};
static struct qotom_xhci_legacy previous;
static uint32_t ext[8192];
static unsigned reads,writes,delays,release_at,fail_read,fail_delay,mutation_at,initial_reads;
static uint32_t mutation,final_support_xor,final_control,final_other_xor,final_vendor_xor;
static int fail_write,ignore_write,final_drift,final_mutated;
static unsigned slot(void) {return (previous.legacy_offset-0x8000)/4;}
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *v) {
    (void)ctx;assert(!b && d==20 && !f && !(off&3) && off<=20);
    if(++reads==fail_read)return 0;
    if(writes && delays>=release_at && !final_mutated) {
        final_mutated=1;
        if(final_drift)return 0;
        ext[slot()]^=final_support_xor;
        ext[0]^=final_other_xor;
        ext[16]^=final_vendor_xor;
        ext[slot()+1]=final_control;
    }
    *v=initial.words[off/4];return 1;
}
static int mmio(void *ctx,uint64_t a,uint32_t *v) {
    (void)ctx;assert(a>=QOTOM_XHCI_BAR && a<=QOTOM_XHCI_BAR+24 && !(a&3));
    if(++reads==fail_read)return 0;
    *v=caps.words[(a-QOTOM_XHCI_BAR)/4];return 1;
}
static int extended(void *ctx,uint64_t a,uint32_t *v) {
    (void)ctx;assert(a>=QOTOM_XHCI_BAR+0x8000 && a<=QOTOM_XHCI_BAR+0xfffc && !(a&3));
    if(++reads==fail_read)return 0;
    *v=ext[(a-QOTOM_XHCI_BAR-0x8000)/4];return 1;
}
static int write_dword(void *ctx,uint64_t a,uint32_t v) {
    (void)ctx;assert(a==QOTOM_XHCI_BAR+previous.legacy_offset && !writes);
    assert(v==(ext[slot()]|0x1000000) && (v&0x10000));
    assert(reads==initial_reads);++writes;
    if(!ignore_write)ext[slot()]=v; /* Failure may still change hardware. */
    return !fail_write;
}
static int delay(void *ctx,uint32_t ms) {
    (void)ctx;assert(ms==10 && writes==1);++delays;
    if(delays==fail_delay)return 0;
    if(delays==release_at)ext[slot()]&=~UINT32_C(0x10000);
    if(delays==mutation_at)ext[slot()]^=mutation;
    return 1;
}
static void reset(void) {
    previous=(struct qotom_xhci_legacy){.count=6,.legacy_offset=0x8460,.control_status=0x2001,
        .headers={{0x8000,0x02000802},{0x8020,0x03000802},{0x8040,0x10cc1},
                  {0x8070,0xfcc0},{0x8460,0x10801},{0x8480,0x5000a}}};
    memset(ext,0,sizeof ext);
    for(unsigned i=0;i<previous.count;++i)ext[(previous.headers[i].offset-0x8000)/4]=previous.headers[i].raw;
    ext[slot()+1]=0x2001;
    reads=writes=delays=fail_read=fail_delay=mutation_at=0;initial_reads=45;
    release_at=1;mutation=final_support_xor=final_other_xor=final_vendor_xor=0;final_control=0x2000;
    fail_write=ignore_write=final_drift=final_mutated=0;
}
static void maximum(void) {
    reset();memset(ext,0,sizeof ext);
    previous=(struct qotom_xhci_legacy){.count=48,.legacy_offset=0x80bc,.control_status=0x2001};
    for(unsigned i=0;i<47;++i)previous.headers[i]=(struct qotom_xhci_ext_header){0x8000+i*4,0x1c0};
    previous.headers[47]=(struct qotom_xhci_ext_header){0x80bc,0x10001};
    for(unsigned i=0;i<48;++i)ext[i]=previous.headers[i].raw;
    ext[48]=0x2001;initial_reads=87;
}
static struct qotom_xhci_handoff_result out;
static void check(enum qotom_xhci_handoff_status expected) {
    memset(&out,0x55,sizeof out);
    assert(qotom_request_xhci_handoff(config,NULL,mmio,NULL,extended,NULL,write_dword,NULL,
        delay,NULL,&initial,&caps,&previous,&out)==expected);
    assert(reads<=274 && writes<=1 && delays<=100 && out.polls<=100);
    assert(out.write_attempted==writes);
    if(expected!=QOTOM_XHCI_HANDOFF_OBSERVED)assert(!out.final_control);
    if(!writes)assert(!out.polls && !out.last_support);
    if(expected==QOTOM_XHCI_HANDOFF_FINAL)assert(out.verify_kind>=1 && out.verify_kind<=6);
    else assert(!out.verify_kind && !out.verify_index && !out.verify_expected && !out.verify_observed);
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    for(unsigned i=1;i<=100;++i) {
        reset();release_at=i;check(QOTOM_XHCI_HANDOFF_OBSERVED);
        assert(out.polls==i && delays==i && out.last_support==0x1000801 && out.final_control==0x2000);
        assert(reads==90+i);
    }
    reset();release_at=101;check(QOTOM_XHCI_HANDOFF_TIMEOUT);assert(out.polls==100 && out.last_support==0x1010801);
    maximum();release_at=100;check(QOTOM_XHCI_HANDOFF_OBSERVED);assert(reads==274);
    for(unsigned i=1;i<=274;++i) {
        maximum();release_at=100;fail_read=i;
        check(i<=87?QOTOM_XHCI_HANDOFF_REFRESH:i<=187?QOTOM_XHCI_HANDOFF_READ:QOTOM_XHCI_HANDOFF_FINAL);
        if(i>187)assert(out.verify_kind==QOTOM_XHCI_VERIFY_COLLECTOR &&
            !out.verify_index && !out.verify_expected &&
            out.verify_observed==(i<=206?QOTOM_XHCI_LEGACY_REFRESH:
                i<=255?QOTOM_XHCI_LEGACY_READ:QOTOM_XHCI_LEGACY_FINAL));
    }
    for(unsigned i=1;i<=100;++i) {
        reset();release_at=101;fail_delay=i;check(QOTOM_XHCI_HANDOFF_DELAY);assert(out.polls==i-1);
    }
    for(unsigned bit=0;bit<32;++bit) {
        if(bit==16)continue;
        reset();mutation_at=1;mutation=UINT32_C(1)<<bit;check(QOTOM_XHCI_HANDOFF_CHANGED);
    }
    reset();fail_write=1;check(QOTOM_XHCI_HANDOFF_WRITE);assert(writes==1 && !delays && ext[slot()]==0x1010801);
    reset();ignore_write=1;check(QOTOM_XHCI_HANDOFF_CHANGED);
    reset();final_drift=1;check(QOTOM_XHCI_HANDOFF_FINAL);
    assert(out.verify_kind==QOTOM_XHCI_VERIFY_COLLECTOR && !out.verify_index &&
        !out.verify_expected && out.verify_observed==QOTOM_XHCI_LEGACY_REFRESH);
    for(unsigned bit=0;bit<32;++bit) {
        reset();final_support_xor=UINT32_C(1)<<bit;check(QOTOM_XHCI_HANDOFF_FINAL);
    }
    reset();final_other_xor=0x10000;check(QOTOM_XHCI_HANDOFF_FINAL);
    assert(out.verify_kind==QOTOM_XHCI_VERIFY_HEADER_RAW && out.verify_index==0 &&
        out.verify_expected==0x02000802 && out.verify_observed==0x02010802);
    reset();final_control=UINT32_MAX;check(QOTOM_XHCI_HANDOFF_FINAL);
    for(unsigned entry=0;entry<6;++entry)for(unsigned bit=0;bit<32;++bit) {
        reset();previous.headers[entry].raw^=UINT32_C(1)<<bit;check(QOTOM_XHCI_HANDOFF_DRIFT);
    }
    reset();ext[slot()]=previous.headers[4].raw=0x108c0;
    previous.legacy_offset=previous.control_status=0;check(QOTOM_XHCI_HANDOFF_INITIAL);
    reset();
    struct qotom_xhci_legacy changed=previous;
    changed.count=5;out=(struct qotom_xhci_handoff_result){0};
    assert(qotom_xhci_final_difference(&previous,&changed,&out));
    assert(out.verify_kind==QOTOM_XHCI_VERIFY_COUNT && out.verify_expected==6 && out.verify_observed==5);
    changed=previous;changed.legacy_offset=0;out=(struct qotom_xhci_handoff_result){0};
    assert(qotom_xhci_final_difference(&previous,&changed,&out));
    assert(out.verify_kind==QOTOM_XHCI_VERIFY_LEGACY_OFFSET && out.verify_expected==0x8460 && !out.verify_observed);
    changed=previous;changed.headers[1].offset+=4;out=(struct qotom_xhci_handoff_result){0};
    assert(qotom_xhci_final_difference(&previous,&changed,&out));
    assert(out.verify_kind==QOTOM_XHCI_VERIFY_HEADER_OFFSET && out.verify_index==1 &&
        out.verify_expected==0x8020 && out.verify_observed==0x8024);
    reset();final_support_xor=0x10000;check(QOTOM_XHCI_HANDOFF_FINAL);
    assert(out.verify_kind==QOTOM_XHCI_VERIFY_SEMAPHORE && out.verify_index==4 &&
        out.verify_expected==0x01000801 && out.verify_observed==0x01010801);
    reset();
    for(unsigned entry=0;entry<6;++entry)for(unsigned bit=0;bit<32;++bit) {
        changed=previous;changed.headers[entry].raw^=UINT32_C(1)<<bit;
        out=(struct qotom_xhci_handoff_result){0};
        assert(qotom_xhci_final_difference(&previous,&changed,&out)==
            (entry==2 && ((UINT32_C(1)<<bit)&QOTOM_XHCI_CMDM_STATUS)?0:
                !qotom_xhci_same_legacy(&previous,&changed,UINT32_C(0x01010000))));
    }
    for(unsigned bit=0;bit<32;++bit) {
        reset();final_vendor_xor=UINT32_C(1)<<bit;
        check((final_vendor_xor&QOTOM_XHCI_CMDM_STATUS)?QOTOM_XHCI_HANDOFF_OBSERVED:QOTOM_XHCI_HANDOFF_FINAL);
    }
    reset();final_vendor_xor=0x10000;check(QOTOM_XHCI_HANDOFF_OBSERVED);
    assert(ext[16]==0xcc1 && out.last_support==0x01000801 && out.final_control==0x2000);
    struct qotom_xhci_ext_header other={0x8044,0x10cc1};
    assert(!qotom_xhci_final_mutable_bits(&other,0x8460));
    other=(struct qotom_xhci_ext_header){0x8040,0x10cc0};
    assert(!qotom_xhci_final_mutable_bits(&other,0x8460));
    reset();previous.count=49;check(QOTOM_XHCI_HANDOFF_DRIFT);
    reset();previous.headers[0].raw^=0x100;check(QOTOM_XHCI_HANDOFF_DRIFT);
    reset();previous.control_status^=1;check(QOTOM_XHCI_HANDOFF_DRIFT);
    const uint32_t bad[]={0x801,0x1000801,0x1010801,0x2010801,0x81010801};
    for(unsigned i=0;i<sizeof bad/sizeof bad[0];++i) {
        reset();ext[slot()]=previous.headers[4].raw=bad[i];check(QOTOM_XHCI_HANDOFF_INITIAL);assert(!writes);
    }
    reset();
    assert(qotom_request_xhci_handoff(NULL,NULL,mmio,NULL,extended,NULL,write_dword,NULL,
        delay,NULL,&initial,&caps,&previous,&out)==QOTOM_XHCI_HANDOFF_ARGUMENT);
    assert(!out.write_attempted && !out.polls && !out.last_support && !out.final_control && !reads);
    puts("PASS bounded xHCI handoff: all release delays, maximum 274 reads, every read/delay failure, drift, timeout and exact DWORD request");
}
