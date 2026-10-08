/* Negative fixture (#484): a subject that writes an MSR.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
void subject_main(void) {
    __asm__ volatile ("wrmsr" : : "c"(0xc0000080u), "a"(0u), "d"(0u));
    leanos_block_forever(13);
}
