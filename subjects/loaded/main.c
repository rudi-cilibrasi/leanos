/* The loaded child (#492).  This subject is never linked into a slot: the
   build admits it as a separate executable (ADR 0024) and embeds its bytes in
   the spawn-loader image's reserved range, and the ring-3 loader there has
   the kernel load it into a spawned child's fresh address space.

   Spawn gave the child exactly one endpoint capability, a send-only copy of
   the parent's endpoint, in slot 0.  The child sends one word through it and
   never runs again: its parent terminates it after receiving the word.  The
   word combines a constant in the text, an initialized data word (which only
   a copy of the admitted data segment provides), and a bss word (which only
   the copy's zero fill provides). */
#include <leanos/subject.h>

#define LOADED_ENDPOINT_SLOT 0u
#define LOADED_WORD 0x4c4f4144ull /* "LOAD" */

static volatile uint64_t data_word = 0x00444100ull;
static volatile uint64_t bss_word;

void subject_main(void) {
    leanos_send_word(LOADED_ENDPOINT_SLOT, LOADED_WORD + data_word + bss_word);
    leanos_block_forever(LOADED_ENDPOINT_SLOT);
}
