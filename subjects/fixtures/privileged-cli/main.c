/* Negative fixture (#484): a subject that disables interrupts.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
void subject_main(void) {
    __asm__ volatile ("cli");
    leanos_block_forever(13);
}
