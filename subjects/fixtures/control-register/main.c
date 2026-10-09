/* Negative fixture (#484): a subject that reads CR3.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
void subject_main(void) {
    uint64_t root;
    __asm__ volatile ("mov %%cr3, %0" : "=r"(root));
    leanos_block_forever(root);
}
