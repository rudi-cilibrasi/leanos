#include "binding.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>
static struct copy_binding_snapshot baseline(void) {
    struct copy_binding_snapshot s = {.address_space=7, .owner_present=1,
                                      .owner=0, .page_count=2};
    for (size_t i=0; i<2; ++i) {
        s.pages[i] = (struct copy_binding_page){.page=i, .object=10+i,
            .read=1, .write=1, .memory_kind=1, .bound=1, .frame=4+i,
            .allocated=1, .allocation_object=10+i, .ancestors={7,7,7},
            .leaf=((4+i)<<12)|7|(UINT64_C(1)<<63)};
    }
    return s;
}
int main(void) {
    struct copy_binding_snapshot s=baseline(), saved=s;
    struct copy_bound_locations out, poison;
    memset(&poison, 0xa5, sizeof(poison));
    assert(copy_binding_validate(&s,0,7,4095,2,1,&out)==COPY_BIND_OK);
    assert(out.count==2 && out.locations[0].frame==4 && out.locations[0].offset==4095);
    assert(out.locations[1].frame==5 && out.locations[1].offset==0);
    assert(memcmp(&s,&saved,sizeof(s))==0);
#define CHECK(reason, caller, space, start, count, dir) do { \
    out=poison; \
    assert(copy_binding_validate(&s,caller,space,start,count,dir,&out)==reason); \
    assert(memcmp(&out,&poison,sizeof(out))==0); \
} while(0)
    CHECK(COPY_BIND_TOO_LONG,0,7,0,17,0);
    CHECK(COPY_BIND_OVERFLOW,0,7,UINT64_MAX,2,0);
    CHECK(COPY_BIND_NONCANONICAL,0,7,UINT64_MAX,1,0);
    CHECK(COPY_BIND_OWNER,1,7,4095,2,0);
    CHECK(COPY_BIND_ADDRESS_SPACE,0,8,4095,2,0);
    CHECK(COPY_BIND_UNMAPPED,0,7,8191,2,0);
    s.pages[1].write=0;
    CHECK(COPY_BIND_PERMISSION,0,7,4095,2,1);
    s=baseline(); s.pages[1].memory_kind=0;
    CHECK(COPY_BIND_KIND,0,7,4095,2,0);
    s=baseline(); s.pages[1].bound=0;
    CHECK(COPY_BIND_RETIRED,0,7,4095,2,0);
    s=baseline(); s.pages[1].allocation_object=12;
    CHECK(COPY_BIND_ALLOCATOR,0,7,4095,2,0);
    s=baseline(); s.pages[1].frame=4;
    CHECK(COPY_BIND_SNAPSHOT,0,7,4095,2,0);
    s.pages[1].object=10; s.pages[1].allocation_object=10;
    CHECK(COPY_BIND_ALIAS,0,7,4095,2,0);
    s=baseline(); s.pages[1].leaf ^= UINT64_C(1)<<12;
    CHECK(COPY_BIND_HARDWARE,0,7,4095,2,0);
    s=baseline(); s.pages[1].ancestors[1] &= ~UINT64_C(2);
    CHECK(COPY_BIND_HARDWARE,0,7,4095,2,1);
    assert(copy_binding_validate(&s,0,7,4095,2,0,&out)==COPY_BIND_OK);
    s=baseline(); s.pages[1].ancestors[0] |= 128;
    CHECK(COPY_BIND_HARDWARE,0,7,4095,2,0);
    s=baseline(); s.pages[0].leaf=0; s.pages[1].write=0;
    CHECK(COPY_BIND_PERMISSION,0,7,4095,2,1);
    s=baseline(); s.pages[1].page=0;
    CHECK(COPY_BIND_SNAPSHOT,0,7,4095,2,0);
    assert(copy_binding_validate(NULL,99,99,UINT64_MAX,0,0,&out)==COPY_BIND_OK);
    assert(out.count==0);
    s=baseline();
    uint64_t slots[2]={0}, protected_frames[2]={4,5};
    struct copy_plan plan;
    assert(copy_binding_validate(&s,0,7,4095,2,0,&out)==COPY_BIND_OK);
    assert(copy_plan_prepare(out.locations,out.count,protected_frames,2,0x700,
                            slots,0x200000,0,&plan)==COPY_PLAN_OK);
    assert(plan.operands[0].source==0x700fff && plan.operands[1].source==0x701000);
    puts("copy binding snapshot: PASS");
}
