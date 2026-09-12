#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "qotom-graphics-state-arm.h"
static uint64_t root[512],pdpt[512],pd[512],pt[4096];static unsigned controls_count;
static int controls(void *opaque,struct lab_ecam_controls *out) {
    (void)opaque;++controls_count;
    *out=(struct lab_ecam_controls){0x0007040600070406,0x80010001,0x100000,0x20,0xd00,2};return 1;
}
static void invalidate(void *opaque,uint64_t address){(void)opaque;(void)address;assert(0);}
static int load32(void *opaque,uint64_t address,uint32_t *value){(void)opaque;(void)address;(void)value;assert(0);}
static void fault(void *opaque){(void)opaque;assert(0);}
static struct pci_enumeration_header header(void) {
    struct pci_enumeration_header h={.device=2};
    const uint32_t words[16]={0x0f318086,0x00100407,0x0300000e,0,
        0xd0000000,0,0xc0000008,0,0x0000f081,0,0,0x0f318086,0,0xd0,0,0x110};
    memcpy(h.words,words,sizeof(words));return h;
}
int main(void) {
    (void)pci_enumerate_segment;
    memset(root,0,sizeof(root));memset(pdpt,0,sizeof(pdpt));memset(pd,0,sizeof(pd));
    struct lab_ecam_root_view view={root,pdpt,pd,pt,0x100000,0x101000,0x102000,0x103000};
    root[0]=view.pdpt_address|7;pdpt[0]=view.pd_address|7;
    for(unsigned i=0;i<8;++i)pd[i]=(view.pt_address+i*4096)|7;
    for(unsigned i=0;i<4096;++i)pt[i]=((uint64_t)i*4096)|UINT64_C(0x8000000000000003);
    struct pci_enumeration_header h=header();
    struct lab_graphics_state_window w={.controls=controls,.invalidate=invalidate,.load32=load32,.fault=fault};
#define ARM() lab_graphics_state_arm(&w,&view,lab_ecam_expected_tables,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h)
    assert(ARM() && w.armed && w.leaf==&pt[512] && w.root==0x100000 && w.window==0x200000);
    const uint64_t aliases[]={QOTOM_GRAPHICS_BAR0,QOTOM_GRAPHICS_BAR0+0x3ff000,
        QOTOM_GRAPHICS_BAR2,QOTOM_GRAPHICS_BAR2+0x0ffff000};
    for(unsigned j=0;j<4;++j)for(unsigned i=0;i<4096;++i) {
        uint64_t saved=pt[i];pt[i]=aliases[j]|1;
        assert(!ARM() && !w.armed && !w.leaf && !w.root && !w.window);pt[i]=saved;
    }
    assert(ARM());h.words[4]^=4096;assert(!ARM() && !w.armed);h.words[4]^=4096;
    struct lab_ecam_firmware_table changed[LAB_ECAM_FIRMWARE_TABLE_COUNT];
    memcpy(changed,lab_ecam_expected_tables,sizeof(changed));changed[0].address^=4;
    assert(!lab_graphics_state_arm(&w,&view,changed,LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h));
    assert(!w.armed && !w.leaf);
    assert(!lab_graphics_state_arm(NULL,&view,lab_ecam_expected_tables,
        LAB_ECAM_FIRMWARE_TABLE_COUNT,0x200000,&h));
    assert(controls_count && ARM());
    puts("PASS graphics arm: exact endpoint/root/firmware binding, full BAR alias exclusion and revoked rearm");
}
