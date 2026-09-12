#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-xhci-legacy.h"
static const struct pci_enumeration_header header={.device=20,.words={0x0f358086,6,0x0c03300e,0,0xd0900004,0}};
static struct qotom_xhci_capabilities prior;
static uint32_t caps[7],ext[8192];
static unsigned reads,failed,extended_reads;
static int final_drift;
static int config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *out) {
    (void)ctx;assert(!b && d==20 && !f && !(off&3) && off<=20);
    if(++reads==failed)return 0;
    *out=header.words[off/4];return 1;
}
static int capability(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;assert(address>=QOTOM_XHCI_BAR && address<=QOTOM_XHCI_BAR+24 && !(address&3));
    if(++reads==failed)return 0;
    *out=caps[(address-QOTOM_XHCI_BAR)/4];
    if(final_drift && extended_reads)*out^=1;
    return 1;
}
static int extended(void *ctx,uint64_t address,uint32_t *out) {
    (void)ctx;assert(address>=QOTOM_XHCI_BAR+0x8000 && address<=QOTOM_XHCI_BAR+0xfffc && !(address&3));
    if(++reads==failed)return 0;
    ++extended_reads;*out=ext[(address-QOTOM_XHCI_BAR-0x8000)/4];return 1;
}
static void reset(void) {
    prior=(struct qotom_xhci_capabilities){{0x1000080,0x7000820,0x84000054,0x200000a,0x200077c1,0x3000,0x2000}};
    memcpy(caps,prior.words,sizeof caps);memset(ext,0,sizeof ext);
    ext[0]=0x00010401;ext[1]=0x2000;ext[4]=0x02000002;
    reads=failed=extended_reads=0;final_drift=0;
}
static struct qotom_xhci_legacy out;
static void check(enum qotom_xhci_legacy_status expected) {
    memset(&out,0x55,sizeof out);
    assert(qotom_collect_xhci_legacy(config,NULL,capability,NULL,extended,NULL,&header,&prior,&out)==expected);
    assert(reads<=87);
    if(expected!=QOTOM_XHCI_LEGACY_OK) {
        const unsigned char *p=(const unsigned char *)&out;
        for(unsigned i=0;i<sizeof out;++i)assert(!p[i]);
    }
}
static void maximum(void) {
    reset();for(unsigned i=0;i<47;++i)ext[i]=0x1c0;
    ext[47]=1;ext[48]=0x2000;
}
int main(void) {
    assert(pci_enumerate_segment(NULL,NULL,NULL).status==PCI_ENUMERATION_INVALID_ARGUMENT);
    reset();check(QOTOM_XHCI_LEGACY_OK);assert(reads==41 && out.count==2 && out.legacy_offset==0x8000 && out.control_status==0x2000);
    maximum();check(QOTOM_XHCI_LEGACY_OK);assert(reads==87 && out.count==48);
    for(unsigned i=1;i<=87;++i){maximum();failed=i;check(i<=19?QOTOM_XHCI_LEGACY_REFRESH:i<=68?QOTOM_XHCI_LEGACY_READ:QOTOM_XHCI_LEGACY_FINAL);}
    maximum();ext[47]=0x1c0;check(QOTOM_XHCI_LEGACY_LIMIT);
    reset();ext[0]=0x101;check(QOTOM_XHCI_LEGACY_OVERLAP);
    reset();ext[4]=1;check(QOTOM_XHCI_LEGACY_DUPLICATE);
    reset();ext[0]=0;check(QOTOM_XHCI_LEGACY_ID);
    reset();ext[0]=UINT32_MAX;check(QOTOM_XHCI_LEGACY_ID);
    reset();ext[1]=UINT32_MAX;check(QOTOM_XHCI_LEGACY_READ);
    reset();final_drift=1;check(QOTOM_XHCI_LEGACY_FINAL);
    for(unsigned i=0;i<7;++i){reset();prior.words[i]^=1;check(QOTOM_XHCI_LEGACY_DRIFT);assert(!extended_reads);}
    reset();caps[4]=prior.words[4]=0x71c1;check(QOTOM_XHCI_LEGACY_OK);assert(!out.count && !extended_reads);
    reset();ext[0]=0xc0;check(QOTOM_XHCI_LEGACY_OK);assert(out.count==1 && !out.legacy_offset);
    reset();caps[4]=prior.words[4]=0x3fff77c1;ext[8191]=1;check(QOTOM_XHCI_LEGACY_POINTER);
    reset();caps[4]=prior.words[4]=0x3fff77c1;ext[8191]=0x102;check(QOTOM_XHCI_LEGACY_POINTER);
    reset();caps[4]=prior.words[4]=0xffff77c1;check(QOTOM_XHCI_LEGACY_POINTER);assert(!extended_reads);
    for(unsigned off=0;off<0x10004;++off){uint64_t a=42;int valid=off>=0x8000 && off<=0xfffc && !(off&3);assert(qotom_xhci_extended_address(off,&a)==valid);assert(a==(valid?QOTOM_XHCI_BAR+off:42));}
    reset();assert(qotom_collect_xhci_legacy(NULL,NULL,capability,NULL,extended,NULL,&header,&prior,&out)==QOTOM_XHCI_LEGACY_ARGUMENT);assert(!reads && !out.count);
    puts("PASS xHCI extended list: relative links, maximum bound, all read failures, overlap/pointer rejection and zero failed output");
}
