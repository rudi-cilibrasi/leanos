/* Freestanding interface for one ring-3 subject built from subjects/ (#484).

   There is no libc and no stable ABI (docs/userspace-abi.md).  The only way
   into the kernel is `int $0x80`: the syscall number goes in RAX, arguments
   in RBX, RCX, RDX (and RSI in the transfer images), and the kernel's word
   comes back in RAX.  Every number is scenario-scoped: an image accepts it
   only from the subject and at the step its script expects, and anything else
   stops the machine (fail-stop).  The numbers below are the ones the IPC
   family of images (blocking-ipc, ipc-stream, three-subject, example-subject)
   give to endpoint receive and send.

   There is no exit syscall.  A subject that is done blocks forever on an
   endpoint nobody sends to (leanos_block_forever).  subject_main must not
   return; if it does, the entry stub executes ud2 and the kernel fail-stops. */
#ifndef LEANOS_SUBJECT_H
#define LEANOS_SUBJECT_H

#include <stdint.h>

#define LEANOS_SYS_RECEIVE 7u
#define LEANOS_SYS_SEND 8u
#define LEANOS_SYS_REPORT 9u

/* The subject's C entry point, called once by subjects/runtime/entry.S on the
   subject's own stack. */
__attribute__((noreturn)) void subject_main(void);

/* One `int $0x80`.  The kernel may hand back words in RAX, RBX and RCX when a
   blocked subject is woken, so all four argument registers are treated as
   clobbered. */
static inline uint64_t leanos_syscall(uint64_t number, uint64_t arg0,
                                      uint64_t arg1, uint64_t arg2) {
    __asm__ volatile ("int $0x80"
                      : "+a"(number), "+b"(arg0), "+c"(arg1), "+d"(arg2)
                      :
                      : "memory");
    return number;
}

/* Send one word on `endpoint`.  The second payload word is always zero. */
static inline uint64_t leanos_send_word(uint64_t endpoint, uint64_t word) {
    return leanos_syscall(LEANOS_SYS_SEND, word, 0, endpoint);
}

/* Block on `endpoint` until a word arrives; the word comes back in RAX. */
static inline uint64_t leanos_receive_word(uint64_t endpoint) {
    return leanos_syscall(LEANOS_SYS_RECEIVE, 0, 0, endpoint);
}

/* The template's "exit": block on an endpoint that no subject sends to.  If
   the kernel ever woke the subject, it would block again. */
__attribute__((noreturn)) static inline void leanos_block_forever(uint64_t endpoint) {
    for (;;)
        (void)leanos_receive_word(endpoint);
}

#endif
