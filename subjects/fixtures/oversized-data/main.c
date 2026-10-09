/* Negative fixture (#484): data larger than the 2048 bytes the stack page leaves
   above the stack.
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
static volatile uint8_t table[4096];
void subject_main(void) {
    table[0] = 1;
    leanos_block_forever(table[4095]);
}
