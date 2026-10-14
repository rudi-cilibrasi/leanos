/* DHCP subject (issue #556), built from subjects/template and linked as
   subject B of the dhcp-subject image (docs/network-subject.md, "DHCP as
   its own subject").

   The subject leases an IPv4 address for the interface: DISCOVER, OFFER,
   REQUEST, ACK and NAK, with retransmission.  The protocol logic is not
   written here: it is `leanos_dhcp_step`, the C the Lean compiler generates
   for LeanOS.Net.DhcpClient.step (LeanOS/Net/DhcpClientC.lean), which the
   build rule passes in as NetDhcp.c and this file includes, so the five
   hooks it calls are inlined over the subject's own frame buffer and its
   own registers.

   It holds no device capability and one frame port, its own; the driver
   subject never gives it an address, only the link record (the hardware
   address) and ticks.  Its life:

     invoke the device (60)        refused: it holds no device capability
     then, for every record:
     receive on endpoint 12 (7)    the driver subject sends the record's
                                   length (RAX) and sequence number (RBX)
     fetch it (64)                 into dhcp_frame, inside this subject's
                                   own window
     step the client               DISCOVER or REQUEST left in place, or none
     send it (65)                  when there is one
     on the ACK: send the lease    to the echo subject on endpoint 13 (8):
                                   the hardware address and the leased
                                   address; the kernel then serves the echo
                                   subject's port, and this subject's next
                                   receive never returns. */
#include <leanos/subject.h>

#define DHCP_FRAME_ENDPOINT 12u
#define DHCP_LEASE_ENDPOINT 13u
#define DHCP_SYS_DEVICE 60u
#define DHCP_SYS_FETCH 64u
#define DHCP_SYS_SEND 65u
#define DHCP_FRAME_BUFFER 1536u
#define DHCP_REGISTERS 10u
/* LeanOS.Net.DhcpClient's registers and phases. */
#define DHCP_REG_PHASE 0u
#define DHCP_REG_MAC 2u
#define DHCP_REG_LEASE 5u
#define DHCP_PHASE_BOUND 3u

#ifdef DHCP_EXTERNAL_FRAME
/* The Qotom lab build (scripts/build-qotom-recovery-lab.py --dhcp-subject):
   the buffer and the registers are at the bottom of the subject's stack
   range, the pages the lab's bounded copy roots alias, and the subject keeps
   no other static data. */
extern uint8_t DHCP_EXTERNAL_FRAME[];
#define dhcp_frame DHCP_EXTERNAL_FRAME
#define dhcp_regs ((uint64_t *)(DHCP_EXTERNAL_FRAME + DHCP_FRAME_BUFFER))
#else
/* In the subject's stack page above the stack (bss). */
static uint8_t dhcp_frame[DHCP_FRAME_BUFFER] __attribute__((aligned(16)));
static uint64_t dhcp_regs[DHCP_REGISTERS];
#endif

/* The hooks of LeanOS.Net.DhcpClientC: the token is the value each
   returns. */
uint64_t dhcp_gen_value(uint64_t t, uint64_t x);
uint64_t dhcp_gen_rd8(uint64_t t, uint32_t off);
uint64_t dhcp_gen_wr8(uint64_t t, uint32_t off, uint32_t v);
uint64_t dhcp_gen_ld(uint64_t t, uint32_t k);
uint64_t dhcp_gen_st(uint64_t t, uint32_t k, uint64_t v);

uint64_t dhcp_gen_value(uint64_t t, uint64_t x) {
    (void)t;
    return x;
}

uint64_t dhcp_gen_rd8(uint64_t t, uint32_t off) {
    (void)t;
    return off < DHCP_FRAME_BUFFER ? dhcp_frame[off] : 0;
}

uint64_t dhcp_gen_wr8(uint64_t t, uint32_t off, uint32_t v) {
    (void)t;
    if (off < DHCP_FRAME_BUFFER) dhcp_frame[off] = (uint8_t)v;
    return 0;
}

uint64_t dhcp_gen_ld(uint64_t t, uint32_t k) {
    (void)t;
    return k < DHCP_REGISTERS ? dhcp_regs[k] : 0;
}

uint64_t dhcp_gen_st(uint64_t t, uint32_t k, uint64_t v) {
    (void)t;
    if (k < DHCP_REGISTERS) dhcp_regs[k] = v;
    return 0;
}

#include "NetDhcp.c"

/* Block on endpoint 12; the kernel wakes the subject with the two payload
   words in RAX and RBX and the delivery flag in RCX. */
static uint64_t dhcp_receive(uint64_t *seq) {
    uint64_t rax = LEANOS_SYS_RECEIVE, rbx = 0, rcx = 0, rdx = DHCP_FRAME_ENDPOINT;
    __asm__ volatile ("int $0x80"
                      : "+a"(rax), "+b"(rbx), "+c"(rcx), "+d"(rdx)
                      :
                      : "memory");
    if (rcx != 1) __builtin_trap();
    *seq = rbx;
    return rax;
}

void subject_main(void) {
    uint64_t expected_seq = 1, handed = 0;
    if (leanos_syscall(DHCP_SYS_DEVICE, 0, 0, 0) == 0) __builtin_trap();
    for (unsigned k = 0; k < DHCP_REGISTERS; ++k) dhcp_regs[k] = 0;
    for (;;) {
        uint64_t seq = 0;
        uint64_t len = dhcp_receive(&seq);
        if (seq != expected_seq) __builtin_trap();
        ++expected_seq;
        if (leanos_syscall(DHCP_SYS_FETCH, (uint64_t)dhcp_frame, 0, 0) != len)
            __builtin_trap();
        uint64_t out = leanos_dhcp_step(0, len);
        if (out != 0 &&
            leanos_syscall(DHCP_SYS_SEND, (uint64_t)dhcp_frame, out, 0) != 0)
            __builtin_trap();
        if (!handed && dhcp_regs[DHCP_REG_PHASE] == DHCP_PHASE_BOUND) {
            handed = 1;
            if (leanos_syscall(LEANOS_SYS_SEND, dhcp_regs[DHCP_REG_MAC],
                    dhcp_regs[DHCP_REG_LEASE], DHCP_LEASE_ENDPOINT) != 0)
                __builtin_trap();
        }
    }
}
