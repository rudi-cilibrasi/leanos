#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../boot/qotom-realtek-bme.h"

enum kind { CONFIG, MMIO };
struct operation { enum kind kind; uint8_t bus,device,function,offset,width; };
static struct operation expected[183];
static unsigned expected_count,reads,writes,fail_at,mutate_at,mutate_value,write_mode;
static struct pci_enumeration_header endpoint,bridge;
static struct pci_capability_snapshot caps;
static struct qotom_rootport_bme_result route;
static struct qotom_realtek_state prior;
static uint32_t endpoint_cfg[64],bridge_cfg[64],mmio_values[6];

static void add_config(uint8_t bus,uint8_t device,uint8_t function,uint8_t offset) {
    expected[expected_count++]=(struct operation){CONFIG,bus,device,function,offset,4};
}
static void add_mmio(uint8_t bus,uint8_t offset,uint8_t width) {
    expected[expected_count++]=(struct operation){MMIO,bus,0,0,offset,width};
}
static void add_bridge(uint8_t function) {
    const uint8_t offsets[34]={0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60,
        0,4,12,52,64,128,144,160,68,72,0,4,12,52,64,128,144,160};
    for(unsigned i=0;i<34;++i)add_config(0,28,function,offsets[i]);
}
static void add_endpoint(uint8_t bus) {
    const uint8_t cfg[8]={0,4,8,12,24,28,32,36};
    const uint8_t offsets[6]={0x40,0x37,0x3c,0x44,0x37,0x40};
    const uint8_t widths[6]={4,1,2,4,1,4};
    for(unsigned i=0;i<8;++i)add_config(bus,0,0,cfg[i]);
    for(unsigned i=0;i<6;++i)add_mmio(bus,offsets[i],widths[i]);
    for(unsigned i=0;i<8;++i)add_config(bus,0,0,cfg[i]);
}
static void add_routed(uint8_t bus,uint8_t function) {
    add_bridge(function);add_endpoint(bus);add_bridge(function);
}
static int config(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint32_t *value) {
    assert(context==endpoint_cfg && reads<expected_count);
    const struct operation *op=&expected[reads];
    assert(op->kind==CONFIG && op->bus==bus && op->device==device &&
        op->function==function && op->offset==offset);
    ++reads;
    if(reads==fail_at)return 0;
    uint32_t *source=bus?endpoint_cfg:bridge_cfg;
    *value=source[offset/4];
    if(reads==mutate_at)*value^=mutate_value;
    return 1;
}
static int mmio(void *context,uint64_t address,uint8_t width,uint32_t *value) {
    assert(context==mmio_values && reads<expected_count);
    const struct operation *op=&expected[reads];
    assert(op->kind==MMIO && address==qotom_realtek_bar(op->bus)+op->offset &&
        width==op->width);
    unsigned index=0;
    const uint8_t offsets[6]={0x40,0x37,0x3c,0x44,0x37,0x40};
    while(index<6 && offsets[index]!=op->offset)++index;
    if(op->offset==0x37 && reads%183>45)index=4;
    ++reads;
    if(reads==fail_at)return 0;
    *value=mmio_values[index];
    if(reads==mutate_at)*value^=mutate_value;
    return 1;
}
static int store(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint16_t value) {
    assert(context==endpoint_cfg && reads==91 && ++writes==1);
    assert(bus==endpoint.bus && !device && !function && offset==4 && value==3);
    if(write_mode!=1 && write_mode!=3)
        endpoint_cfg[1]=(endpoint_cfg[1]&UINT32_C(0xffff0000))|3;
    return write_mode<2;
}
static void setup(uint8_t bus) {
    endpoint=(struct pci_enumeration_header){.bus=bus};
    uint32_t bar=(uint32_t)qotom_realtek_bar(bus);
    const uint32_t endpoint_words[16]={0x816810ec,0x00100007,0x02000007,16,
        0,0,bar|4,0,(bar-0x4000)|12,0,0,0x012310ec,0,64,0,261};
    memcpy(endpoint.words,endpoint_words,sizeof endpoint_words);
    bridge=(struct pci_enumeration_header){.device=28,.function=bus-1};
    const uint32_t bridge_words[16]={bus==1?0x0f488086:0x0f4c8086,0x00100007,
        0x0604000e,0x00810010,0,0,(bus<<16)|(bus<<8),
        bus==1?0x2000e0e0:0x2000d0d0,bus==1?0xd080d080:0xd060d060,
        0x0001fff1,0,0,0,0x40,0,bus==1?0x00100105:0x00100305};
    memcpy(bridge.words,bridge_words,sizeof bridge_words);
    memset(endpoint_cfg,0,sizeof endpoint_cfg);memset(bridge_cfg,0,sizeof bridge_cfg);
    memcpy(endpoint_cfg,endpoint_words,sizeof endpoint_words);
    memcpy(bridge_cfg,bridge_words,sizeof bridge_words);bridge_cfg[1]=0x00100003;
    caps=(struct pci_capability_snapshot){.count=4};
    const unsigned offsets[4]={64,128,144,160};
    const uint32_t raws[4]={21135376,36869,40973,3355639809u};
    for(unsigned i=0;i<4;++i) {
        caps.headers[i]=(struct pci_capability_header){offsets[i],raws[i]};
        bridge_cfg[offsets[i]/4]=raws[i];
    }
    bridge_cfg[17]=0x8000;bridge_cfg[18]=0x100000;
    route=(struct qotom_rootport_bme_result){1,7,3};
    const uint32_t values[6]={0x2f900d00,0,0,0x0002ff0e,0,0x2f900d00};
    memcpy(mmio_values,values,sizeof values);
    prior=(struct qotom_realtek_state){values[0],values[1],values[2],
        values[3],values[4],values[5]};
    expected_count=reads=writes=fail_at=mutate_at=mutate_value=write_mode=0;
    add_routed(bus,bus-1);add_config(bus,0,0,4);add_config(bus,0,0,4);
    add_routed(bus,bus-1);add_config(bus,0,0,4);
    assert(expected_count==183);
}
static enum qotom_realtek_bme_status clear(struct qotom_realtek_bme_result *out) {
    memset(out,0xff,sizeof *out);
    return qotom_clear_realtek_bme(config,endpoint_cfg,mmio,mmio_values,store,endpoint_cfg,
        &endpoint,&bridge,&caps,QOTOM_ROOTPORT_OK,&route,QOTOM_REALTEK_OK,&prior,out);
}
int main(void) {
    (void)pci_enumerate_segment;
    assert(!qotom_realtek_stopped(NULL));assert(!qotom_realtek_same_state(NULL,NULL));
    struct qotom_realtek_bme_result out;
    for(uint8_t bus=1;bus<=3;bus+=2) {
        setup(bus);assert(clear(&out)==QOTOM_REALTEK_BME_OK);
        assert(reads==183 && writes==1 && out.attempted==1 &&
            out.before_command==7 && out.after_command==3);
        for(unsigned n=1;n<=183;++n) {
            setup(bus);fail_at=n;
            enum qotom_realtek_bme_status status=n<=90?QOTOM_REALTEK_BME_REFRESH:
                n==91?QOTOM_REALTEK_BME_COMMAND:n==92?QOTOM_REALTEK_BME_READBACK:
                QOTOM_REALTEK_BME_FINAL;
            assert(clear(&out)==status && reads==n && writes==(n>91));
            assert(out.attempted==(n>91) && out.before_command==(n>91?7:0));
            assert(out.after_command==(n>92?3:0));
        }
        for(unsigned mode=1;mode<=3;++mode) {
            setup(bus);write_mode=mode;
            enum qotom_realtek_bme_status status=mode==1?QOTOM_REALTEK_BME_READBACK:
                QOTOM_REALTEK_BME_WRITE;
            assert(clear(&out)==status && reads==(mode==1?92:91) && writes==1);
            assert(out.attempted==1 && out.before_command==7 &&
                out.after_command==(mode==1?7:0));
        }
        for(unsigned phase=0;phase<2;++phase)for(unsigned field=0;field<6;++field) {
            setup(bus);mutate_at=(phase?135:43)+field;mutate_value=1;
            assert(clear(&out)==(phase?QOTOM_REALTEK_BME_FINAL:QOTOM_REALTEK_BME_STATE));
            assert(reads==(phase?182:90));
        }
        for(unsigned field=0;field<6;++field)for(unsigned bit=0;bit<32;++bit) {
            setup(bus);((uint32_t *)&prior)[field]^=UINT32_C(1)<<bit;
            assert(clear(&out)==(field==3?QOTOM_REALTEK_BME_STATE:QOTOM_REALTEK_BME_PRIOR));
            assert(reads==(field==3?90:0) && !writes);
        }
        setup(bus);endpoint_cfg[1]=0x00100003;
        assert(clear(&out)==QOTOM_REALTEK_BME_REFRESH && reads==36);
        setup(bus);mutate_at=92;mutate_value=4;
        assert(clear(&out)==QOTOM_REALTEK_BME_READBACK && reads==92 && out.after_command==7);
        setup(bus);mutate_at=183;mutate_value=4;
        assert(clear(&out)==QOTOM_REALTEK_BME_FINAL && reads==183 && out.after_command==7);
    }
    setup(1);
#define CALL(c,m,w,e,b,p,r,s,o) qotom_clear_realtek_bme(c,endpoint_cfg,m,mmio_values,w, \
        endpoint_cfg,e,b,p,QOTOM_ROOTPORT_OK,r,QOTOM_REALTEK_OK,s,o)
    assert(CALL(NULL,mmio,store,&endpoint,&bridge,&caps,&route,&prior,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,NULL,store,&endpoint,&bridge,&caps,&route,&prior,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,mmio,NULL,&endpoint,&bridge,&caps,&route,&prior,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,mmio,store,NULL,&bridge,&caps,&route,&prior,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,mmio,store,&endpoint,NULL,&caps,&route,&prior,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,mmio,store,&endpoint,&bridge,NULL,&route,&prior,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,mmio,store,&endpoint,&bridge,&caps,NULL,&prior,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,mmio,store,&endpoint,&bridge,&caps,&route,NULL,&out)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(CALL(config,mmio,store,&endpoint,&bridge,&caps,&route,&prior,NULL)==QOTOM_REALTEK_BME_ARGUMENT);
    assert(!reads && !writes);
    for(unsigned status=1;status<=9;++status) {
        setup(1);memset(&out,0xff,sizeof out);
        assert(qotom_clear_realtek_bme(config,endpoint_cfg,mmio,mmio_values,store,
            endpoint_cfg,&endpoint,&bridge,&caps,QOTOM_ROOTPORT_OK,&route,status,&prior,
            &out)==QOTOM_REALTEK_BME_PRIOR);
        assert(!reads && !writes && !out.attempted && !out.before_command && !out.after_command);
    }
#undef CALL
    puts("PASS Realtek BME: both stopped endpoints, exact183 reads, all failures, state drift, prior fields, ambiguous writes and reassertion");
}
