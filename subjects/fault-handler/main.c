/* Fault handler subject (#488), built from subjects/template and linked as
   subject C of the fault-handler image.  The image binds divide errors
   raised by subject A to this subject at boot.  C blocks receiving on the
   fault endpoint 14; when A faults, the kernel suspends A and wakes C with
   exactly the typed fault record:

     RAX  class word: contained-reason code | vector << 8 (1 = #DE, vector 0)
     RBX  faulting subject
     RCX  address word: the saved RIP of the faulting instruction
     RDX  error word (0: #DE pushes none)

   C reports the record (syscall 64), replies "terminate" (syscall 65, the only
   decision in this slice), and blocks forever on endpoint 13.  The transcript
   is scripts/expectations/fault-handler.transcript. */
#include <leanos/subject.h>

#define FAULT_ENDPOINT 14u
#define IDLE_ENDPOINT 13u
#define SYS_FAULT_REPORT 64u
#define SYS_FAULT_REPLY 65u
#define DECISION_TERMINATE 1u
#define DECISION_INVALID 2u
#define CLASS_DIVIDE_ERROR 1u

struct fault_record {
    uint64_t class_word;
    uint64_t faulting;
    uint64_t address;
    uint64_t error_word;
};

/* Block on the fault endpoint until the kernel delivers a record; the four
   record words come back in RAX, RBX, RCX and RDX. */
static struct fault_record receive_fault(void) {
    uint64_t rax = LEANOS_SYS_RECEIVE, rbx = 0, rcx = 0, rdx = FAULT_ENDPOINT;
    __asm__ volatile ("int $0x80"
                      : "+a"(rax), "+b"(rbx), "+c"(rcx), "+d"(rdx)
                      :
                      : "memory");
    struct fault_record record = { rax, rbx, rcx, rdx };
    return record;
}

void subject_main(void) {
    struct fault_record record = receive_fault();
    (void)leanos_syscall(SYS_FAULT_REPORT, record.class_word, record.faulting,
                         record.address);
    /* Terminate is the only decision; anything other than the bound #DE
       record is answered with a decision the kernel refuses (fail-stop). */
    uint64_t decision = record.class_word == CLASS_DIVIDE_ERROR &&
                                record.error_word == 0
                            ? DECISION_TERMINATE
                            : DECISION_INVALID;
    (void)leanos_syscall(SYS_FAULT_REPLY, decision, record.faulting, FAULT_ENDPOINT);
    leanos_block_forever(IDLE_ENDPOINT);
}
