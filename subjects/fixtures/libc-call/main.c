/* Negative fixture (#484): a subject that calls a libc function (there is no
   libc).
   scripts/test-build-subject.sh requires the build rule to reject it. */
#include <leanos/subject.h>
extern int puts(const char *text);
void subject_main(void) {
    puts("hello");
    leanos_block_forever(13);
}
