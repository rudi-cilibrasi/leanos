/* Negative fixture (#484): a subject that writes an I/O port.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
void subject_main(void) {
    __asm__ volatile ("outb %%al, $0x80" : : "a"(0));
    leanos_block_forever(13);
}
