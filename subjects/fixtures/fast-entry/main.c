/* Negative fixture (#484): a subject that enters the kernel with syscall instead of
   int $0x80.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
void subject_main(void) {
    __asm__ volatile ("syscall" : : : "rcx", "r11", "memory");
    leanos_block_forever(13);
}
