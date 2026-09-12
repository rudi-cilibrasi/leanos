#ifndef LEANOS_QOTOM_AHCI_PORT_H
#define LEANOS_QOTOM_AHCI_PORT_H
#include "qotom-ahci-capabilities.h"

struct qotom_ahci_port {
    uint32_t command_before, interrupt_enable, task_file, sata_status;
    uint32_t active, issued, command_after;
};
enum qotom_ahci_port_status {
    QOTOM_AHCI_PORT_OK, QOTOM_AHCI_PORT_ARGUMENT, QOTOM_AHCI_PORT_PRIOR,
    QOTOM_AHCI_PORT_REFRESH, QOTOM_AHCI_PORT_DRIFT, QOTOM_AHCI_PORT_READ,
    QOTOM_AHCI_PORT_ABSENT, QOTOM_AHCI_PORT_FINAL
};
static inline int qotom_ahci_port1_profile(const struct qotom_ahci_capabilities *c) {
    return c && c->capability==UINT32_C(0xc720ff01) &&
        (c->control==UINT32_C(0x80000000) || c->control==UINT32_C(0x80000002)) &&
        c->ports==2 && c->version==UINT32_C(0x10300) && c->extended==UINT32_C(0x38);
}
static inline int qotom_ahci_globals_equal(const struct qotom_ahci_capabilities *a,
                                         const struct qotom_ahci_capabilities *b) {
    return a->capability==b->capability && a->control==b->control &&
        a->ports==b->ports && a->version==b->version && a->extended==b->extended;
}
/* Address selection only. Firmware/root/resource and private UC window binding
 * are caller obligations, as are immutable, nonaliasing, serialized inputs. */
static inline int qotom_ahci_port_address(uint32_t offset,uint64_t *out) {
    if(!out || (offset!=0x194 && offset!=0x198 && offset!=0x1a0 &&
        offset!=0x1a8 && offset!=0x1b4 && offset!=0x1b8)) return 0;
    *out=QOTOM_AHCI_BAR+offset;return 1;
}
/* 37 reads: two complete 15-read global/resource collections bracket seven
 * port samples. The command register is sampled on both sides of IE/TFD/SSTS/
 * SACT/CI. All raw values are observations, not halt or outstanding-DMA proof.
 * No port-zero read, write, polling or reset. Every failure zeroes all output. */
static inline enum qotom_ahci_port_status qotom_collect_ahci_port(
        pci_enumeration_read config,void *config_context,
        qotom_ahci_mmio_read global,void *global_context,
        qotom_ahci_mmio_read port,void *port_context,
        const struct pci_enumeration_header *header,
        enum qotom_ahci_status prior_status,const struct qotom_ahci_capabilities *prior,
        struct qotom_ahci_port *out) {
    if(out)*out=(struct qotom_ahci_port){0};
    if(!config || !global || !port || !header || !prior || !out) return QOTOM_AHCI_PORT_ARGUMENT;
    if(prior_status!=QOTOM_AHCI_OK || !qotom_ahci_port1_profile(prior)) return QOTOM_AHCI_PORT_PRIOR;
    struct qotom_ahci_capabilities fresh;
    if(qotom_collect_ahci_capabilities(config,config_context,global,global_context,header,&fresh)!=QOTOM_AHCI_OK)
        return QOTOM_AHCI_PORT_REFRESH;
    if(!qotom_ahci_globals_equal(prior,&fresh)) return QOTOM_AHCI_PORT_DRIFT;
    const uint32_t offsets[7]={0x198,0x194,0x1a0,0x1a8,0x1b4,0x1b8,0x198};
    uint32_t values[7];
    for(unsigned i=0;i<7;++i) {
        uint64_t address;
        if(!qotom_ahci_port_address(offsets[i],&address)) return QOTOM_AHCI_PORT_ARGUMENT;
        if(!port(port_context,address,&values[i])) return QOTOM_AHCI_PORT_READ;
        if(values[i]==UINT32_MAX) return QOTOM_AHCI_PORT_ABSENT;
    }
    if(qotom_collect_ahci_capabilities(config,config_context,global,global_context,header,&fresh)!=QOTOM_AHCI_OK ||
        !qotom_ahci_globals_equal(prior,&fresh)) return QOTOM_AHCI_PORT_FINAL;
    *out=(struct qotom_ahci_port){values[0],values[1],values[2],values[3],values[4],values[5],values[6]};
    return QOTOM_AHCI_PORT_OK;
}
#endif
