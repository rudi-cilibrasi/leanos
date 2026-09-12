#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-realtek-state.h"
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
static void check(struct model *m,enum qotom_realtek_status expected,uint32_t reads) {
    struct qotom_realtek_state out;memset(&out,0xa5,sizeof(out));
    assert(qotom_collect_realtek_state(config,m,mmio,m,&m->header,&out)==expected);
    assert(m->reads==reads);
    if (expected!=QOTOM_REALTEK_OK) {
        struct qotom_realtek_state zero={0};assert(!memcmp(&out,&zero,sizeof(out)));
    } else {
        assert(out.transmit_before==m->values[0] && out.command_before==m->values[1] &&
            out.interrupt_mask==m->values[2] && out.receive==m->values[3] &&
            out.command_after==m->values[4] && out.transmit_after==m->values[5]);
    }
}
int main(void) {
    (void)pci_enumerate_segment;
    for (uint8_t bus=1;bus<=3;bus+=2) {
        struct model m=model(bus);check(&m,QOTOM_REALTEK_OK,22);
        for (uint32_t fail=1;fail<=22;++fail) {
            m=model(bus);m.fail=fail;check(&m,fail>=9 && fail<=14?QOTOM_REALTEK_MMIO_READ:QOTOM_REALTEK_CONFIG_READ,fail);
        }
        const uint8_t offsets[8]={0,4,8,12,24,28,32,36};
        const uint32_t masks[8]={UINT32_MAX,65535,UINT32_MAX,0xff0000,UINT32_MAX,UINT32_MAX,UINT32_MAX,UINT32_MAX};
        for (uint32_t i=0;i<8;++i) for (uint32_t bit=0;bit<32;++bit) {
            uint32_t mask=UINT32_C(1)<<bit;
            m=model(bus);m.header.words[offsets[i]/4]^=mask;
            check(&m,(mask&masks[i])?QOTOM_REALTEK_HEADER:QOTOM_REALTEK_OK,(mask&masks[i])?0:22);
            for (uint32_t phase=0;phase<2;++phase) {
                m=model(bus);m.mutate=1+i+phase*14;m.xor_value=mask;
                check(&m,(mask&masks[i])?QOTOM_REALTEK_DRIFT:QOTOM_REALTEK_OK,(mask&masks[i])?m.mutate:22);
            }
        }
        for (uint32_t i=0;i<6;++i) {
            m=model(bus);m.values[i]=(i==1 || i==4)?255:(i==2?65535:UINT32_MAX);
            check(&m,QOTOM_REALTEK_ABSENT,9+i);
            if (i==1 || i==2 || i==4) {
                m=model(bus);m.values[i]=(i==2)?65536:256;check(&m,QOTOM_REALTEK_WIDTH,9+i);
            }
        }
        for (uint32_t i=0;i<6;i+=5) for (uint32_t bit=0;bit<32;++bit) {
            m=model(bus);m.values[i]^=UINT32_C(1)<<bit;
            int bad=(UINT32_C(0x7cc00000)&(UINT32_C(1)<<bit))!=0;
            check(&m,bad?QOTOM_REALTEK_REVISION:QOTOM_REALTEK_OK,bad?9+i:22);
        }
        for (uint32_t i=1;i<=4;i+=3) {
            m=model(bus);m.values[i]=16;check(&m,QOTOM_REALTEK_RESET,9+i);
            m=model(bus);m.values[i]=0x8c;check(&m,QOTOM_REALTEK_OK,22);
        }
        for (uint32_t b=0;b<256;++b) if (b!=1 && b!=3) {
            m=model(bus);m.header.bus=(uint8_t)b;check(&m,QOTOM_REALTEK_HEADER,0);
        }
        m=model(bus);m.header.device=1;check(&m,QOTOM_REALTEK_HEADER,0);
        m=model(bus);m.header.function=1;check(&m,QOTOM_REALTEK_HEADER,0);
        for (uint32_t off=0;off<4096;++off) for (uint8_t width=0;width<9;++width) {
            uint64_t addr=0xdead;
            int allowed=(off==0x37 && width==1)||(off==0x3c && width==2)||((off==0x40 || off==0x44)&&width==4);
            assert(qotom_realtek_state_address(bus,off,width,&addr)==allowed);
            assert(addr==(allowed?qotom_realtek_bar(bus)+off:0xdead));
        }
    }
    struct model m=model(1);struct qotom_realtek_state out;
    assert(qotom_collect_realtek_state(NULL,&m,mmio,&m,&m.header,&out)==QOTOM_REALTEK_ARGUMENT);
    assert(qotom_collect_realtek_state(config,&m,NULL,&m,&m.header,&out)==QOTOM_REALTEK_ARGUMENT);
    assert(qotom_collect_realtek_state(config,&m,mmio,&m,NULL,&out)==QOTOM_REALTEK_ARGUMENT);
    assert(qotom_collect_realtek_state(config,&m,mmio,&m,&m.header,NULL)==QOTOM_REALTEK_ARGUMENT);
    assert(!m.reads && !qotom_realtek_header_valid(NULL));
    uint64_t addr=123;
    assert(!qotom_realtek_state_address(2,0x40,4,&addr) && addr==123);
    assert(!qotom_realtek_state_address(1,0x40,4,NULL));
    puts("PASS bounded Realtek observation: two resources, 22-read order, all read failures, binding drift, revision/reset/width and aperture checks");
}
