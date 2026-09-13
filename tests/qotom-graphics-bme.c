#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-graphics-bme.h"

enum kind { CONFIG, MMIO };
struct operation { enum kind kind; uint8_t offset; };
static struct operation expected[127];
static unsigned expected_count,reads,writes,fail_at,mutate_at,mutate_value,write_mode;
static struct pci_enumeration_header endpoint;
static struct qotom_graphics_state prior;
static uint32_t config_words[16],observed[QOTOM_GRAPHICS_SAMPLE_WORDS];

static void add_config(uint8_t offset) {
    expected[expected_count++]=(struct operation){CONFIG,offset};
}
static void add_observation(void) {
    for(unsigned i=0;i<16;++i)add_config((uint8_t)(i*4));
    for(unsigned i=0;i<30;++i)expected[expected_count++]=(struct operation){MMIO,0};
    for(unsigned i=0;i<16;++i)add_config((uint8_t)(i*4));
}
static int config(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    assert(context==config_words && reads<expected_count);
    assert(expected[reads].kind==CONFIG && expected[reads].offset==offset);
    assert(!bus && device==2 && !function);++reads;
    if(reads==fail_at)return 0;
    *value=config_words[offset/4];
    if(reads==mutate_at)*value^=mutate_value;
    return 1;
}
static int mmio(void *context,uint64_t address,uint32_t *value) {
    assert(context==observed && reads<expected_count && expected[reads].kind==MMIO);
    unsigned base=reads<62?16:80,slot=reads-base;uint64_t wanted;
    assert(slot<30 && qotom_graphics_state_address((slot%15)/5,slot%5,&wanted));
    assert(address==wanted);++reads;
    if(reads==fail_at)return 0;
    *value=observed[slot];
    if(reads==mutate_at)*value^=mutate_value;
    return 1;
}
static int store(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint16_t value) {
    assert(context==config_words && reads==63 && ++writes==1);
    assert(!bus && device==2 && !function && offset==4 && value==3);
    if(write_mode!=1 && write_mode!=3)
        config_words[1]=(config_words[1]&UINT32_C(0xffff0000))|3;
    return write_mode<2;
}
static void setup(void) {
    endpoint=(struct pci_enumeration_header){.device=2};
    const uint32_t words[16]={0x0f318086,0x00100007,0x0300000e,0,
        0xd0000000,0,0xc0000008,0,0x0000f081,0,0,0x0f318086,0,0xd0,0,0x110};
    memcpy(endpoint.words,words,sizeof words);memcpy(config_words,words,sizeof words);
    memset(&prior,0,sizeof prior);
    for(unsigned sample=0;sample<2;++sample)for(unsigned engine=0;engine<3;++engine)
        prior.words[sample*15+engine*5+4]=0x200;
    memcpy(observed,prior.words,sizeof observed);
    expected_count=reads=writes=fail_at=mutate_at=mutate_value=write_mode=0;
    add_observation();add_config(4);add_config(4);add_observation();add_config(4);
    assert(expected_count==127);
}
static enum qotom_graphics_bme_status clear(struct qotom_graphics_bme_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_clear_graphics_bme(config,config_words,mmio,observed,store,
        config_words,&endpoint,QOTOM_GRAPHICS_OK,&prior,out);
}
int main(void) {
    (void)pci_enumerate_segment;
    assert(!qotom_graphics_quiet(NULL));assert(!qotom_graphics_same_state(NULL,NULL));
    setup();assert(qotom_graphics_quiet(&prior));assert(qotom_graphics_same_state(&prior,&prior));
    struct qotom_graphics_bme_result out;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_OK && reads==127 && writes==1);
    assert(out.attempted==1 && out.before_command==7 && out.after_command==3);
    for(unsigned n=1;n<=127;++n) {
        setup();fail_at=n;
        enum qotom_graphics_bme_status status=n<=62?QOTOM_GRAPHICS_BME_REFRESH:
            n==63?QOTOM_GRAPHICS_BME_COMMAND:n==64?QOTOM_GRAPHICS_BME_READBACK:
            QOTOM_GRAPHICS_BME_FINAL;
        assert(clear(&out)==status && reads==n && writes==(n>63));
        assert(out.attempted==(n>63) && out.before_command==(n>63?7:0));
        assert(out.after_command==(n>64?3:0));
    }
    for(unsigned mode=1;mode<=3;++mode) {
        setup();write_mode=mode;
        enum qotom_graphics_bme_status status=mode==1?QOTOM_GRAPHICS_BME_READBACK:
            QOTOM_GRAPHICS_BME_WRITE;
        assert(clear(&out)==status && reads==(mode==1?64:63) && writes==1);
        assert(out.attempted==1 && out.before_command==7 &&
            out.after_command==(mode==1?7:0));
    }
    setup();mutate_at=17;mutate_value=1;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_STATE && reads==62 && !writes);
    setup();mutate_at=81;mutate_value=1;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_FINAL && reads==126 && writes==1);
    setup();mutate_at=64;mutate_value=4;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_READBACK && out.after_command==7);
    setup();mutate_at=127;mutate_value=4;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_FINAL && out.after_command==7);
    setup();prior.words[3]=1;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_PRIOR && !reads && !writes);
    setup();prior.words[4]=0;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_PRIOR && !reads && !writes);
    setup();prior.words[15]=1;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_PRIOR && !reads && !writes);
    setup();prior.words[2]=prior.words[17]=1;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_STATE && reads==62 && !writes);
    setup();config_words[1]=0x00100003;
    assert(clear(&out)==QOTOM_GRAPHICS_BME_REFRESH && reads==2 && !writes);
#define CALL(c,m,w,e,p,o) qotom_clear_graphics_bme(c,config_words,m,observed,w, \
        config_words,e,QOTOM_GRAPHICS_OK,p,o)
    setup();
    assert(CALL(NULL,mmio,store,&endpoint,&prior,&out)==QOTOM_GRAPHICS_BME_ARGUMENT);
    assert(CALL(config,NULL,store,&endpoint,&prior,&out)==QOTOM_GRAPHICS_BME_ARGUMENT);
    assert(CALL(config,mmio,NULL,&endpoint,&prior,&out)==QOTOM_GRAPHICS_BME_ARGUMENT);
    assert(CALL(config,mmio,store,NULL,&prior,&out)==QOTOM_GRAPHICS_BME_ARGUMENT);
    assert(CALL(config,mmio,store,&endpoint,NULL,&out)==QOTOM_GRAPHICS_BME_ARGUMENT);
    assert(CALL(config,mmio,store,&endpoint,&prior,NULL)==QOTOM_GRAPHICS_BME_ARGUMENT);
    assert(!reads && !writes);
#undef CALL
    for(unsigned status=1;status<=7;++status) {
        setup();memset(&out,0xff,sizeof out);
        assert(qotom_clear_graphics_bme(config,config_words,mmio,observed,store,
            config_words,&endpoint,status,&prior,&out)==QOTOM_GRAPHICS_BME_PRIOR);
        assert(!reads && !writes && !out.attempted && !out.before_command && !out.after_command);
    }
    puts("PASS graphics BME: quiet retained state, exact127 reads, one word7to3, all failures, drift and reassertion");
}
