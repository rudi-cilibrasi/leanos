#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-broadcom-assign-arm.h"

static unsigned stores;
static int store(void *context,uint8_t bus,uint8_t device,uint8_t function,
        uint8_t offset,uint16_t value) {
    (void)context;(void)bus;(void)device;(void)function;(void)offset;(void)value;
    ++stores;return 0;
}
int main(void) {
    (void)pci_enumerate_segment;
    struct pci_enumeration_header endpoint={.bus=2,.words={
        0x435314e4,0x00100006,0x02800001,0x10,0xd0700004,0,0,0,
        0,0,0,0x04d814e4,0,0x40,0,0x105}};
    struct pci_capability_snapshot caps={.count=4,.headers={
        {0x40,0xce035801},{0x58,0x00784809},{0x48,0x0080d005},{0xd0,0x00010010}}};
    struct pci_express_observation pcie={PCI_EXPRESS_OK,0xd0,0x05908fa0,0x00190000};
    struct qotom_broadcom_d3_result d3={1,6,0,2,0x19,0x4008,1,0x400b};
    struct qotom_broadcom_assign_policy policy={2,0,0,0x435314e4,0,
        UINT64_C(0x80100000000),2};
    uint64_t contract=1;
    enum qotom_broadcom_d3_status d3_status=QOTOM_BROADCOM_D3_OK;
    struct lab_broadcom_assign_window window={.store16=store};
#define ARM() lab_broadcom_assign_arm(&window,contract,d3_status,&d3,&endpoint,&caps,&pcie,&policy)
    assert(ARM() && window.armed==1);
    for(unsigned bit=0;bit<64;++bit) {
        assert(ARM());contract^=UINT64_C(1)<<bit;assert(!ARM() && !window.armed);
        contract^=UINT64_C(1)<<bit;
    }
    for(unsigned status=1;status<=13;++status) {
        assert(ARM());d3_status=(enum qotom_broadcom_d3_status)status;
        assert(!ARM() && !window.armed);d3_status=QOTOM_BROADCOM_D3_OK;
    }
    for(unsigned field=0;field<8;++field)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());((uint32_t *)&d3)[field]^=UINT32_C(1)<<bit;
        int accepted=field==3 && d3.pending_polls>=2 && d3.pending_polls<=100;
        if(accepted)assert(ARM());else assert(!ARM() && !window.armed);
        ((uint32_t *)&d3)[field]^=UINT32_C(1)<<bit;
    }
    for(unsigned word=0;word<16;++word)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());endpoint.words[word]^=UINT32_C(1)<<bit;
        int relevant=word==0 || word==2 || word==4 || word==5 || word==11 || word==13 ||
            (word==1 && bit<16) || (word==3 && bit>=16 && bit<24);
        if(relevant)assert(!ARM() && !window.armed);else assert(ARM());
        endpoint.words[word]^=UINT32_C(1)<<bit;
    }
    for(unsigned i=0;i<4;++i)for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());caps.headers[i].raw^=UINT32_C(1)<<bit;
        assert(!ARM() && !window.armed);caps.headers[i].raw^=UINT32_C(1)<<bit;
    }
    for(unsigned status=1;status<=8;++status) {
        assert(ARM());pcie.status=status;assert(!ARM() && !window.armed);pcie.status=PCI_EXPRESS_OK;
    }
    for(unsigned bit=0;bit<32;++bit) {
        assert(ARM());pcie.device_capabilities^=UINT32_C(1)<<bit;
        assert(!ARM() && !window.armed);pcie.device_capabilities^=UINT32_C(1)<<bit;
        assert(ARM());pcie.device_control_status^=UINT32_C(1)<<bit;
        assert(!ARM() && !window.armed);pcie.device_control_status^=UINT32_C(1)<<bit;
    }
    /* Every policy bit: only narrowing the configuration-write set or the
       Command-set bits keeps the policy assignable. */
    for(unsigned field=0;field<7;++field)for(unsigned bit=0;bit<64;++bit) {
        assert(ARM());((uint64_t *)&policy)[field]^=UINT64_C(1)<<bit;
        int narrower=(field==5 && (bit==32 || bit==43)) || (field==6 && bit==1);
        if(narrower)assert(ARM());else assert(!ARM() && !window.armed);
        ((uint64_t *)&policy)[field]^=UINT64_C(1)<<bit;
    }
    assert(ARM());window.store16=0;assert(!ARM() && !window.armed);window.store16=store;
    assert(ARM());assert(!lab_broadcom_assign_arm(&window,contract,d3_status,NULL,
        &endpoint,&caps,&pcie,&policy) && !window.armed);
    assert(ARM());assert(!lab_broadcom_assign_arm(&window,contract,d3_status,&d3,
        NULL,&caps,&pcie,&policy) && !window.armed);
    assert(ARM());assert(!lab_broadcom_assign_arm(&window,contract,d3_status,&d3,
        &endpoint,NULL,&pcie,&policy) && !window.armed);
    assert(ARM());assert(!lab_broadcom_assign_arm(&window,contract,d3_status,&d3,
        &endpoint,&caps,NULL,&policy) && !window.armed);
    assert(ARM());assert(!lab_broadcom_assign_arm(&window,contract,d3_status,&d3,
        &endpoint,&caps,&pcie,NULL) && !window.armed);
    assert(!lab_broadcom_assign_arm(NULL,contract,d3_status,&d3,&endpoint,&caps,&pcie,&policy));
    assert(!stores);
    puts("PASS Broadcom assign arm: contract, exact D3 record, endpoint/capability/PCIe binding and assignable policy");
}
