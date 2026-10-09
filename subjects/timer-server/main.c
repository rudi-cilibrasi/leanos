/* Timer server (#487), built from subjects/template and linked as subject C
   of the timer-server image.  The kernel keeps the PIT and its interrupt;
   this subject holds the timer capability and decides the alarm policy
   (LeanOS.TimerServer.policy): a request is refused when its count is
   outside 1..65535 or when the client already has QUOTA alarms
   outstanding, and accepted otherwise.  Accepted alarms are queued; the head
   is armed through the timer capability (syscall 90).

   C blocks receiving on its endpoint 12.  It is woken with three words:

     RAX  the request's count, or the expiry bits for a timer expiry
     RBX  the request's second word (unused)
     RCX  the sender: a client subject, or 0 for the kernel's expiry

   It answers a request and blocks again in one step (syscall 91, the reply
   word in RBX).  On an expiry it wakes the client at the head of its queue
   by signalling that client's wake notification (syscall 92), arms the
   next alarm if any, and blocks (syscall 7).  The transcript is
   scripts/expectations/timer-server.transcript. */
#include <leanos/subject.h>

#define SERVER_ENDPOINT 12u
#define WAKE_NOTIFICATION 13u
#define SYS_TIMER_ARM 90u
#define SYS_REPLY_RECEIVE 91u
#define SYS_WAKE 92u
#define SENDER_KERNEL 0u
#define MAX_COUNT 65535u
#define QUOTA 1u
#define SUBJECTS 4u
#define QUEUE_SLOTS 4u
#define WAKE_BITS 1u
#define REPLY_ACCEPTED 1u
#define REPLY_REFUSED_BOUND 0x202u
#define REPLY_REFUSED_QUOTA 0x402u

struct message {
    uint64_t word0;
    uint64_t word1;
    uint64_t sender;
};

/* One blocking receive on the server endpoint, entered with `number`
   (7 receive, or 91 reply-and-receive with the reply word in RBX). */
static struct message receive(uint64_t number, uint64_t reply) {
    uint64_t rax = number, rbx = reply, rcx = 0, rdx = SERVER_ENDPOINT;
    __asm__ volatile ("int $0x80"
                      : "+a"(rax), "+b"(rbx), "+c"(rcx), "+d"(rdx)
                      :
                      : "memory");
    struct message message = { rax, rbx, rcx };
    return message;
}

/* In the subject's stack page above the stack (bss). */
static uint64_t outstanding[SUBJECTS];
static uint64_t queue_client[QUEUE_SLOTS];
static uint64_t queue_count[QUEUE_SLOTS];
static uint64_t queue_head, queue_length, armed;

static uint64_t policy(uint64_t client, uint64_t count) {
    if (count == 0 || count > MAX_COUNT) return REPLY_REFUSED_BOUND;
    if (client >= SUBJECTS || outstanding[client] >= QUOTA ||
        queue_length == QUEUE_SLOTS)
        return REPLY_REFUSED_QUOTA;
    return REPLY_ACCEPTED;
}

/* Arm the head alarm through the timer capability, if none is armed. */
static void arm_head(void) {
    if (armed || queue_length == 0) return;
    if (leanos_syscall(SYS_TIMER_ARM, queue_count[queue_head], 0, 0) == REPLY_ACCEPTED)
        armed = 1;
}

void subject_main(void) {
    struct message message = receive(LEANOS_SYS_RECEIVE, 0);
    for (;;) {
        if (message.sender == SENDER_KERNEL) {
            armed = 0;
            if (queue_length != 0) {
                uint64_t client = queue_client[queue_head];
                queue_head = (queue_head + 1) % QUEUE_SLOTS;
                queue_length = queue_length - 1;
                outstanding[client] = outstanding[client] - 1;
                (void)leanos_syscall(SYS_WAKE, client, WAKE_BITS, WAKE_NOTIFICATION);
            }
            arm_head();
            message = receive(LEANOS_SYS_RECEIVE, 0);
            continue;
        }
        uint64_t reply = policy(message.sender, message.word0);
        if (reply == REPLY_ACCEPTED) {
            uint64_t slot = (queue_head + queue_length) % QUEUE_SLOTS;
            queue_client[slot] = message.sender;
            queue_count[slot] = message.word0;
            queue_length = queue_length + 1;
            outstanding[message.sender] = outstanding[message.sender] + 1;
            arm_head();
        }
        message = receive(SYS_REPLY_RECEIVE, reply);
    }
}
