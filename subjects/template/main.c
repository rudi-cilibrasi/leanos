/* Subject template (#484): copy this directory to subjects/<name>/ and see
   docs/subjects.md.  Every .c and .S file in the directory is compiled
   freestanding (no libc, no SSE or x87) and linked with subjects/runtime/
   entry.S, which calls subject_main on the subject's own stack. */
#include <leanos/subject.h>

/* The endpoint this subject blocks on when it is done.  Endpoint numbers are
   scenario-scoped: the kernel script of the image this subject is linked
   into decides which endpoints exist. */
#define TEMPLATE_IDLE_ENDPOINT 13u

void subject_main(void) {
    /* Work goes here: only plain C, and only the leanos_* calls from
       <leanos/subject.h> enter the kernel. */
    leanos_block_forever(TEMPLATE_IDLE_ENDPOINT);
}
