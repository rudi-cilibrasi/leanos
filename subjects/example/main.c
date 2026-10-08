/* Example subject (#484), built from subjects/template and linked as subject
   C of the example-subject image.  It sends one word on endpoint 12 and then
   blocks forever on endpoint 13, which nobody sends to: there is no exit
   syscall.  Subject A receives the word and reports it; the transcript is
   scripts/expectations/example-subject.transcript. */
#include <leanos/subject.h>

#define EXAMPLE_ENDPOINT 12u
#define EXAMPLE_IDLE_ENDPOINT 13u
#define EXAMPLE_WORD 0x5355424aull /* "SUBJ" */

/* Lives in the subject's stack page above the stack: shows bss placement. */
static volatile uint64_t words_sent;

void subject_main(void) {
    leanos_send_word(EXAMPLE_ENDPOINT, EXAMPLE_WORD);
    words_sent = words_sent + 1;
    leanos_block_forever(EXAMPLE_IDLE_ENDPOINT);
}
