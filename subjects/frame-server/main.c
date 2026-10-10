/* Frame server (#486), built from subjects/template and linked as subject C
   of the frame-server image (docs/frame-server.md).

   The server holds the pool capability over two pool frames (indices 0 and
   1, read and write) and keeps the allocation policy in its own memory: the
   budget each client's capability allows and which client holds which pool
   frame.  It blocks on endpoint 12.  The kernel wakes it with one request:

     RAX  request: 1 = a frame, 2 = release the client's budget
     RBX  the client, attested by the kernel

   and the server answers with one decision (syscall 91), after which it
   blocks on endpoint 12 again:

     RBX  op | rights << 8: 1 grant, 2 refuse (budget exhausted),
          3 refuse (pool exhausted), 5 revoke the client's budget
     RCX  the client
     RDX  the pool frame (grant only)

   The policy is LeanOS.FrameServer.serverPolicy: grant the first free pool
   frame with the pool rights while the client is below its budget, refuse
   with the true reason otherwise; a release revokes the client's budget.
   The kernel chooses nothing: it checks each decision against the generated
   witness (FrameServer.frameServerCheck) and applies it exactly. */
#include <leanos/subject.h>

#define REQUEST_ENDPOINT 12u
#define SYS_DECIDE 91u
#define REQUEST_FRAME 1u
#define REQUEST_RELEASE 2u
#define OP_GRANT 1u
#define OP_REFUSE_BUDGET 2u
#define OP_REFUSE_POOL 3u
#define OP_REVOKE 5u
#define POOL_FRAMES 2u
#define POOL_RIGHTS 3u     /* read 1 | write 2 */
#define CLIENTS 3u
#define NO_FRAME 0xffu

struct request {
    uint64_t kind;
    uint64_t client;
};

/* In the subject's stack page above the stack (bss). */
static uint64_t budget[CLIENTS];
static uint64_t holder[POOL_FRAMES];

static struct request call(uint64_t number, uint64_t arg0, uint64_t arg1,
                           uint64_t arg2) {
    uint64_t rax = number, rbx = arg0, rcx = arg1, rdx = arg2;
    __asm__ volatile ("int $0x80"
                      : "+a"(rax), "+b"(rbx), "+c"(rcx), "+d"(rdx)
                      :
                      : "memory");
    struct request request = { rax, rbx };
    return request;
}

static uint64_t usage(uint64_t client) {
    uint64_t count = 0;
    for (uint64_t frame = 0; frame < POOL_FRAMES; ++frame)
        if (holder[frame] == client) count = count + 1;
    return count;
}

static uint64_t first_free(void) {
    for (uint64_t frame = 0; frame < POOL_FRAMES; ++frame)
        if (holder[frame] == 0) return frame;
    return NO_FRAME;
}

void subject_main(void) {
    budget[1] = 1;
    budget[2] = 2;
    struct request request = call(LEANOS_SYS_RECEIVE, 0, 0, REQUEST_ENDPOINT);
    for (;;) {
        uint64_t client = request.client < CLIENTS ? request.client : 0;
        uint64_t word = OP_REFUSE_BUDGET;
        uint64_t frame = 0;
        if (request.kind == REQUEST_RELEASE) {
            for (uint64_t f = 0; f < POOL_FRAMES; ++f)
                if (holder[f] == client) holder[f] = 0;
            budget[client] = 0;
            word = OP_REVOKE;
        } else if (usage(client) < budget[client]) {
            frame = first_free();
            if (frame == NO_FRAME) {
                word = OP_REFUSE_POOL;
                frame = 0;
            } else {
                holder[frame] = client;
                word = OP_GRANT | POOL_RIGHTS << 8;
            }
        }
        request = call(SYS_DECIDE, word, request.client, frame);
    }
}
