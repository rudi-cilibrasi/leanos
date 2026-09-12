#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-realtek-route.h"
struct model {
    struct pci_enumeration_header header;
    uint32_t values[6],reads,fail,mutate,xor_value;
};
static struct model model(uint8_t bus) {
    struct model m={0};
    m.header.bus=bus;
    uint32_t words[16]={0x816810ec,0x00100007,0x02000007,16,
        bus==1?0xe001:0xd001,0,(uint32_t)qotom_realtek_bar(bus)|4,0,
        ((uint32_t)qotom_realtek_bar(bus)-0x4000)|12,0,0,0x012310ec,0,64,0,261};
    memcpy(m.header.words,words,sizeof(words));
    /* Modeled values, not a physical LeanOS observation. */
    uint32_t values[6]={0x2c800800,0,0,0,0,0x2c800800};
    memcpy(m.values,values,sizeof(values));return m;
}
static int finish(struct model *m,uint32_t *v) {
    ++m->reads;
    if (m->reads==m->fail) return 0;
    if (m->reads==m->mutate) *v^=m->xor_value;
    return 1;
}
static int config(void *ctx,uint8_t bus,uint8_t device,uint8_t function,uint8_t offset,uint32_t *v) {
    struct model *m=ctx;
    const uint8_t offsets[8]={0,4,8,12,24,28,32,36};
    assert(bus==m->header.bus && !device && !function);
    assert(m->reads<8 || (m->reads>=14 && m->reads<22));
    uint32_t i=m->reads<8?m->reads:m->reads-14;
    assert(offset==offsets[i]);*v=m->header.words[offset/4];return finish(m,v);
}
static int mmio(void *ctx,uint64_t address,uint8_t width,uint32_t *v) {
    struct model *m=ctx;const uint8_t offsets[6]={0x40,0x37,0x3c,0x44,0x37,0x40};
    const uint8_t widths[6]={4,1,2,4,1,4};
    assert(m->reads>=8 && m->reads<14);uint32_t i=m->reads-8;
    assert(address==qotom_realtek_bar(m->header.bus)+offsets[i] && width==widths[i]);
    *v=m->values[i];return finish(m,v);
}
static struct model endpoint;
static struct pci_enumeration_header bridge;
static struct pci_capability_snapshot caps;
static uint32_t bridge_config[64],reads,fail_at,change_at,change_word,change_mask;
static const uint8_t bridge_offsets[34]={0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60,
    0,4,12,52,64,128,144,160,68,72,0,4,12,52,64,128,144,160};
static int routed_config(void *ctx,uint8_t b,uint8_t d,uint8_t f,uint8_t off,uint32_t *v) {
    (void)ctx;unsigned n=reads++;
    if(b) {
        assert(n>=34 && n<56);
        if(reads==fail_at)return 0;
        return config(&endpoint,b,d,f,off,v);
    }
    assert(d==28 && f==bridge.function && (n<34 || n>=56));
    assert(off==bridge_offsets[n<34?n:n-56]);
    if(reads==change_at)bridge_config[change_word]^=change_mask;
    if(reads==fail_at)return 0;
    *v=bridge_config[off/4];return 1;
}
static int routed_mmio(void *ctx,uint64_t address,uint8_t width,uint32_t *v) {
    (void)ctx;++reads;
    if(reads==fail_at)return 0;
    return mmio(&endpoint,address,width,v);
}
static void setup(uint8_t bus) {
    endpoint=model(bus);bridge=(struct pci_enumeration_header){.device=28,.function=bus-1};
    uint32_t words[16]={bus==1?0x0f488086:0x0f4c8086,0x100007,0x0604000e,0x810010,
        0,0,(bus<<16)|(bus<<8),bus==1?0x2000e0e0:0x2000d0d0,
        bus==1?0xd080d080:0xd060d060,0x1fff1,0,0,0,0x40,0,bus==1?0x100105:0x100305};
    memcpy(bridge.words,words,sizeof words);memset(bridge_config,0,sizeof bridge_config);
    memcpy(bridge_config,words,sizeof words);bridge_config[1]=0x100003;
    caps=(struct pci_capability_snapshot){.count=4};
    const unsigned offsets[]={64,128,144,160};
    const uint32_t raws[]={21135376,36869,40973,3355639809u};
    for(unsigned i=0;i<4;++i){caps.headers[i]=(struct pci_capability_header){offsets[i],raws[i]};bridge_config[offsets[i]/4]=raws[i];}
    bridge_config[17]=0x8000;bridge_config[18]=0x100000;
    reads=fail_at=change_at=change_word=change_mask=0;
}
static uint32_t collect(enum qotom_rootport_bme_status status,const struct qotom_rootport_bme_result *prior) {
    struct qotom_realtek_state out,zero={0};memset(&out,0xff,sizeof out);
    uint32_t result=qotom_collect_realtek_routed_state(routed_config,NULL,routed_mmio,NULL,
        &endpoint.header,&bridge,&caps,status,prior,&out);
    if(result)assert(!memcmp(&out,&zero,sizeof out));
    else assert(out.transmit_before==endpoint.values[0] && out.transmit_after==endpoint.values[5]);
    return result;
}
int main(void) {
    (void)pci_enumerate_segment;
    struct qotom_rootport_bme_result prior={1,7,3};
    for(uint8_t bus=1;bus<=3;bus+=2) {
        setup(bus);assert(!collect(QOTOM_ROOTPORT_OK,&prior) && reads==90);
        for(unsigned n=1;n<=90;++n) {
            setup(bus);fail_at=n;
            uint32_t expected=n<=34?11:n>56?12:(n>=43 && n<=48?QOTOM_REALTEK_MMIO_READ:QOTOM_REALTEK_CONFIG_READ);
            assert(collect(QOTOM_ROOTPORT_OK,&prior)==expected && reads==n);
        }
        for(unsigned phase=0;phase<2;++phase)for(unsigned word=0;word<16;++word)for(unsigned bit=0;bit<32;++bit) {
            setup(bus);change_at=phase?57:1;change_word=word;change_mask=UINT32_C(1)<<bit;
            uint32_t mask=word==1?0x0010ffff:word==7?0xffff:UINT32_MAX;
            uint32_t result=collect(QOTOM_ROOTPORT_OK,&prior);
            assert(result==((mask&change_mask)?(phase?12:11):0));
        }
        for(unsigned phase=0;phase<2;++phase) {
            setup(bus);change_at=phase?57:1;change_word=18;change_mask=1u<<21;
            assert(collect(QOTOM_ROOTPORT_OK,&prior)==(phase?12:11));
            setup(bus);bridge_config[16]^=1;assert(collect(QOTOM_ROOTPORT_OK,&prior)==11);
        }
        for(unsigned word=6;word<=11;++word)if(word!=7)for(unsigned bit=0;bit<32;++bit) {
            setup(bus);bridge.words[word]^=1u<<bit;
            assert(collect(QOTOM_ROOTPORT_OK,&prior)==10 && !reads);
        }
        setup(bus);bridge.function=bus==1?2:0;
        assert(collect(QOTOM_ROOTPORT_OK,&prior)==10 && !reads);
        for(unsigned status=1;status<=8;++status){setup(bus);assert(collect(status,&prior)==10 && !reads);}
        for(unsigned i=0;i<3;++i)for(unsigned bit=0;bit<32;++bit) {
            struct qotom_rootport_bme_result bad=prior;
            if(i==0)bad.attempted^=1u<<bit;
            if(i==1)bad.before_command^=1u<<bit;
            if(i==2)bad.after_command^=1u<<bit;
            setup(bus);assert(collect(QOTOM_ROOTPORT_OK,&bad)==10 && !reads);
        }
        setup(bus);assert(collect(QOTOM_ROOTPORT_OK,NULL)==10 && !reads);
    }
    setup(1);struct qotom_realtek_state out,zero={0};
    assert(qotom_collect_realtek_routed_state(NULL,NULL,routed_mmio,NULL,&endpoint.header,&bridge,&caps,QOTOM_ROOTPORT_OK,&prior,&out)==QOTOM_REALTEK_ARGUMENT);
    assert(!memcmp(&out,&zero,sizeof out));
    assert(qotom_collect_realtek_routed_state(routed_config,NULL,NULL,NULL,&endpoint.header,&bridge,&caps,QOTOM_ROOTPORT_OK,&prior,&out)==QOTOM_REALTEK_ARGUMENT);
    assert(qotom_collect_realtek_routed_state(routed_config,NULL,routed_mmio,NULL,&endpoint.header,&bridge,&caps,QOTOM_ROOTPORT_OK,&prior,NULL)==QOTOM_REALTEK_ARGUMENT);
    assert(qotom_collect_realtek_routed_state(routed_config,NULL,routed_mmio,NULL,&endpoint.header,&bridge,NULL,QOTOM_ROOTPORT_OK,&prior,&out)==10);
    assert(qotom_collect_realtek_routed_state(routed_config,NULL,routed_mmio,NULL,&endpoint.header,NULL,&caps,QOTOM_ROOTPORT_OK,&prior,&out)==10);
    assert(qotom_collect_realtek_routed_state(routed_config,NULL,routed_mmio,NULL,NULL,&bridge,&caps,QOTOM_ROOTPORT_OK,&prior,&out)==10);
    assert(!reads && !memcmp(&out,&zero,sizeof out));
    puts("PASS routed Realtek reads: exact 90 operations, both paths, all failures, bridge drift, invalid routing and prior transitions");
}
