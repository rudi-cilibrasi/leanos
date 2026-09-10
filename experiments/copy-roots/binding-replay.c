#include "binding.h"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
int main(void) {
    uint64_t w[35];
    int read;
    while ((read=scanf("%" SCNu64,&w[0]))==1) {
        for (size_t i=1;i<35;++i) if (scanf("%" SCNu64,&w[i])!=1) return 2;
        struct copy_binding_snapshot s={.address_space=w[5], .owner_present=w[6],
                                        .owner=w[7], .page_count=w[8]};
        for (size_t i=0;i<2;++i) {
            const uint64_t *r=&w[9+13*i];
            s.pages[i]=(struct copy_binding_page){r[0],r[1],r[2],r[3],r[4],r[5],
                r[6],r[7],r[8],{r[9],r[10],r[11]},r[12]};
        }
        struct copy_bound_locations out, poison;
        memset(&poison,0xa5,sizeof(poison)); out=poison;
        enum copy_binding_result result=copy_binding_validate(&s,w[0],w[1],w[2],w[3],(unsigned)w[4],&out);
        if (result!=COPY_BIND_OK) {
            if (memcmp(&out,&poison,sizeof(out))) return 3;
            printf("%u\n",(unsigned)result);
        } else {
            printf("0 %" PRIu64,out.count);
            for (size_t i=0;i<out.count;++i)
                printf(" %" PRIu64 " %" PRIu64,out.locations[i].frame,out.locations[i].offset);
            putchar('\n');
        }
    }
    return read==EOF ? 0 : 2;
}
