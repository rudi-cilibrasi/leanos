/* Negative fixture (#484): a subject that touches SSE state, which is denied at
   CPL3.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
void subject_main(void) {
    __asm__ volatile ("pxor %xmm0, %xmm0");
    leanos_block_forever(13);
}
