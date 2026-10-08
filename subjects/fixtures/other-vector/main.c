/* Negative fixture (#484): a subject that raises a software interrupt other than
   vector 0x80.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
void subject_main(void) {
    __asm__ volatile ("int $0x81");
    leanos_block_forever(13);
}
