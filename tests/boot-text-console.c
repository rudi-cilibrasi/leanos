#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../include/boot_text_console.h"
extern void leanos_register_boundary_target(const char *, void *);

static void u32(uint8_t *p, uint32_t x) {
    for (unsigned i=0;i<4;++i) p[i]=(uint8_t)(x>>(8*i));
}
static void surface(uint8_t *b) {
    memset(b,0,96); u32(b,48); u32(b+8,8); u32(b+12,32);
    u32(b+16,0xb8000); u32(b+24,10); u32(b+28,3); u32(b+32,2);
    b[36]=16; b[37]=2; u32(b+44,8);
}
int main(void) {
    leanos_register_boundary_target("leanos_boot_text_surface",
        (void *)(uintptr_t)&leanos_boot_text_surface);
    struct boot_text_geometry g;
    uint8_t b[96]; surface(b);
    assert(boot_text_parse(b,48,&g));
    for(unsigned n=0;n<48;++n) assert(!boot_text_parse(b,n,&g));
    const unsigned offsets[]={0,4,12,16,20,24,28,32,36,37,40,44};
    for(unsigned i=0;i<sizeof(offsets)/sizeof(*offsets);++i) {
        surface(b); b[offsets[i]]=0xff;
        assert(!boot_text_parse(b,48,&g));
    }
    surface(b); memcpy(b+40,b+8,32); u32(b,80); u32(b+76,8);
    assert(!boot_text_parse(b,80,&g)); /* duplicate surface */
    surface(b); u32(b+8,99); assert(!boot_text_parse(b,48,&g));
    surface(b); u32(b,56); assert(!boot_text_parse(b,56,&g)); /* premature end */
    surface(b); assert(boot_text_parse(b,48,&g));
    uint16_t cells[16386];
    for(unsigned i=0;i<16386;++i) cells[i]=0xa55a;
    struct boot_text_console c={0};
    assert(boot_text_enable(&c,&g,cells+1));
    assert(cells[0]==0xa55a && cells[4]==0xa55a && cells[5]==0xa55a);
    boot_text_putc(&c,'A'); boot_text_putc(&c,'B'); boot_text_putc(&c,'C');
    boot_text_putc(&c,'\n'); assert(c.row==1 && c.column==0);
    boot_text_putc(&c,'D'); boot_text_putc(&c,'E'); boot_text_putc(&c,'F');
    boot_text_putc(&c,'\n'); assert(cells[1]==0x0744 && cells[3]==0x0746);
    assert(cells[6]==0x0720 && cells[8]==0x0720);
    boot_text_putc(&c,'X'); boot_text_putc(&c,'\r'); boot_text_putc(&c,'Y');
    assert(cells[6]==0x0759);
    c.busy=1; boot_text_putc(&c,'Z'); assert(c.column==1); c.busy=0;
    boot_text_putc(&c,1); assert(cells[7]==0x073f);
    for(unsigned i=0;i<100000;++i) boot_text_putc(&c,'a'+i%26);
    for(unsigned y=0;y<2;++y) for(unsigned x=3;x<5;++x)
        assert(cells[1+y*5+x]==0xa55a);
    for(unsigned i=11;i<16386;++i) assert(cells[i]==0xa55a);
    boot_text_disable(&c); uint32_t col=c.column;
    boot_text_putc(&c,'Q'); assert(c.column==col);
    g.address=0; assert(!boot_text_enable(&c,&g,0));
    g=(struct boot_text_geometry){.address=0xb8000,.pitch=512,.width=160,.height=64,.kind=2,.bits=16};
    assert(boot_text_enable(&c,&g,cells+1));
    for(unsigned i=0;i<50000;++i) boot_text_putc(&c,'x');
    assert(cells[0]==0xa55a && cells[16385]==0xa55a);
    assert(!leanos_boot_text_surface(2,16,0xb8000,512,160,65));
    assert(!leanos_boot_text_surface(2,16,0xb8000,512,UINT64_MAX,64));
    assert(!leanos_boot_text_surface(2,16,UINT64_MAX,512,160,64));
    for (unsigned field=0;field<6;++field) for (unsigned bit=32;bit<64;++bit) {
        uint64_t raw[6]={2,16,0xb8000,160,80,25};
        raw[field] |= UINT64_C(1) << bit;
        assert(!leanos_boot_text_surface(raw[0],raw[1],raw[2],raw[3],raw[4],raw[5]));
    }
    puts("Boot text parsing, generated gate, scrolling and guarded writes passed");
}
