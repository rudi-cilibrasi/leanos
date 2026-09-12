#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-graphics-state.h"

struct model { struct pci_enumeration_header header;unsigned reads,fail,mutate;uint32_t xor_value; };
static struct model model(void) {
    struct model m={0};m.header.device=2;
    const uint32_t words[16]={0x0f318086,0x00100407,0x0300000e,0,
        0xd0000000,0,0xc0000008,0,0x0000f081,0,0,0x0f318086,0,0xd0,0,0x110};
    memcpy(m.header.words,words,sizeof(words));return m;
}
static int finish(struct model *m,uint32_t *value) {
    ++m->reads;if(m->reads==m->fail)return 0;
    if(m->reads==m->mutate)*value^=m->xor_value;
    return 1;
}
static int config(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    struct model *m=context;assert(!bus && device==2 && !function);
    unsigned index=m->reads<16?m->reads:m->reads-46;
    assert(index<16 && offset==index*4);*value=m->header.words[index];return finish(m,value);
}
static int mmio(void *context,uint64_t address,uint32_t *value) {
    struct model *m=context;unsigned index=m->reads-16,sample=index/15,slot=index%15;
    uint64_t expected;assert(m->reads>=16 && m->reads<46 && sample<2);
    assert(qotom_graphics_state_address(slot/5,slot%5,&expected) && address==expected);
    *value=(slot%5==4)?0x200:(sample*100+slot);return finish(m,value);
}
static void check(struct model *m,enum qotom_graphics_status expected,unsigned reads) {
    struct qotom_graphics_state out;memset(&out,0xa5,sizeof(out));
    enum qotom_graphics_status actual=
        qotom_collect_graphics_state(config,m,mmio,m,&m->header,&out);
    if(actual!=expected)fprintf(stderr,"expected status %u, got %u after %u reads\n",
        expected,actual,m->reads);
    assert(actual==expected);
    assert(m->reads==reads);
    if(expected!=QOTOM_GRAPHICS_OK) {
        struct qotom_graphics_state zero={0};assert(!memcmp(&out,&zero,sizeof(out)));
    } else for(unsigned i=0;i<30;++i)
        assert(out.words[i]==(i%5==4?0x200:(i/15)*100+i%15));
}
int main(void) {
    (void)pci_enumerate_segment;
    struct model m=model();check(&m,QOTOM_GRAPHICS_OK,62);
    for(unsigned fail=1;fail<=62;++fail) {
        m=model();m.fail=fail;check(&m,fail<=16 || fail>=47?
            QOTOM_GRAPHICS_CONFIG_READ:QOTOM_GRAPHICS_MMIO_READ,fail);
    }
    m=model();m.mutate=47;m.xor_value=1;check(&m,QOTOM_GRAPHICS_DRIFT,47);
    m=model();m.mutate=47+15;m.xor_value=1;check(&m,QOTOM_GRAPHICS_OK,62);
    m=model();m.mutate=17;m.xor_value=UINT32_MAX;
    check(&m,QOTOM_GRAPHICS_ABSENT,17);
    for(unsigned engine=0;engine<3;++engine)for(unsigned reg=0;reg<5;++reg) {
        uint64_t address=0;assert(qotom_graphics_state_address(engine,reg,&address));
        assert(address>=QOTOM_GRAPHICS_BAR0 &&
               address<QOTOM_GRAPHICS_BAR0+QOTOM_GRAPHICS_BAR0_SIZE);
    }
    uint64_t unchanged=42;
    assert(!qotom_graphics_state_address(3,0,&unchanged) && unchanged==42);
    assert(!qotom_graphics_state_address(0,5,&unchanged) && unchanged==42);
    assert(!qotom_graphics_state_address(0,0,NULL));
    m=model();m.header.words[4]^=4096;check(&m,QOTOM_GRAPHICS_HEADER,0);
    m=model();m.header.device=3;check(&m,QOTOM_GRAPHICS_HEADER,0);
    m=model();struct qotom_graphics_state out;
    assert(qotom_collect_graphics_state(NULL,&m,mmio,&m,&m.header,&out)==QOTOM_GRAPHICS_ARGUMENT);
    assert(qotom_collect_graphics_state(config,&m,NULL,&m,&m.header,&out)==QOTOM_GRAPHICS_ARGUMENT);
    assert(qotom_collect_graphics_state(config,&m,mmio,&m,NULL,&out)==QOTOM_GRAPHICS_ARGUMENT);
    assert(qotom_collect_graphics_state(config,&m,mmio,&m,&m.header,NULL)==QOTOM_GRAPHICS_ARGUMENT);
    puts("PASS bounded Valleyview graphics state: exact header, 62-read order, all read failures, drift, absence and address checks");
}
