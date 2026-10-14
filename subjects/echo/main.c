/* Echo subject (issue #556), built from subjects/template and linked as
   subject C of the dhcp-subject image (docs/network-subject.md, "DHCP as
   its own subject").

   The subject answers ARP, ICMP echo and UDP echo (port 7) for the address
   the DHCP subject leased, and for no other.  The protocol logic is not
   written here: it is `leanos_net_reply`, the C the Lean compiler generates
   for LeanOS.Net.Echo.reply (LeanOS/Net/EchoC.lean), included as NetEcho.c
   as in subjects/net.  Unlike subjects/net, the subject never takes an
   address from the driver: it receives the lease over IPC from the DHCP
   subject (LeanOS.DhcpSubject).

   It holds no device capability and one frame port, its own; the kernel
   serves that port only after the DHCP subject's hand-off.  Its life:

     invoke the device (60)        refused: it holds no device capability
     fetch a frame (64)            refused: the endpoint serves the DHCP
                                   subject until the hand-off
     receive on endpoint 13 (7)    the lease: the hardware address (RAX) and
                                   the leased IPv4 address (RBX), sent by the
                                   DHCP subject
     then, for every record:
     receive on endpoint 12 (7)    the driver subject sends the record's
                                   length (RAX) and sequence number (RBX)
     fetch it (64)                 into echo_frame, inside this subject's
                                   own window
     compute the reply in place
     send the reply (65)           skipped when there is nothing to answer

   A record below 14 bytes (a tick) is never an Ethernet frame and draws no
   reply. */
#include <leanos/subject.h>

#define ECHO_FRAME_ENDPOINT 12u
#define ECHO_LEASE_ENDPOINT 13u
#define ECHO_SYS_DEVICE 60u
#define ECHO_SYS_FETCH 64u
#define ECHO_SYS_SEND 65u
#define ECHO_FRAME_BUFFER 1536u
/* A refused request: bit 63 and the reason. */
#define ECHO_REFUSED (UINT64_C(1) << 63)

#ifdef ECHO_EXTERNAL_FRAME
/* The Qotom lab build (scripts/build-qotom-recovery-lab.py --dhcp-subject):
   the buffer is the bottom of the subject's stack range, the pages the lab's
   bounded copy roots alias, and the subject keeps no other static data. */
extern uint8_t ECHO_EXTERNAL_FRAME[];
#define echo_frame ECHO_EXTERNAL_FRAME
#else
/* In the subject's stack page above the stack (bss). */
static uint8_t echo_frame[ECHO_FRAME_BUFFER] __attribute__((aligned(16)));
#endif

/* The hooks of LeanOS.Net.EchoC: the token is the value each returns. */
uint64_t net_gen_value(uint64_t t, uint64_t x);
uint64_t net_gen_rd8(uint64_t t, uint32_t off);
uint64_t net_gen_wr8(uint64_t t, uint32_t off, uint32_t v);

uint64_t net_gen_value(uint64_t t, uint64_t x) {
    (void)t;
    return x;
}

uint64_t net_gen_rd8(uint64_t t, uint32_t off) {
    (void)t;
    return off < ECHO_FRAME_BUFFER ? echo_frame[off] : 0;
}

uint64_t net_gen_wr8(uint64_t t, uint32_t off, uint32_t v) {
    (void)t;
    if (off < ECHO_FRAME_BUFFER) echo_frame[off] = (uint8_t)v;
    return 0;
}

#include "NetEcho.c"

/* Block on `endpoint`; the kernel wakes the subject with the two payload
   words in RAX and RBX and the delivery flag in RCX. */
static uint64_t echo_receive(uint64_t endpoint, uint64_t *second) {
    uint64_t rax = LEANOS_SYS_RECEIVE, rbx = 0, rcx = 0, rdx = endpoint;
    __asm__ volatile ("int $0x80"
                      : "+a"(rax), "+b"(rbx), "+c"(rcx), "+d"(rdx)
                      :
                      : "memory");
    if (rcx != 1) __builtin_trap();
    *second = rbx;
    return rax;
}

void subject_main(void) {
    uint64_t ip = 0, last_seq = 0;
    if (leanos_syscall(ECHO_SYS_DEVICE, 0, 0, 0) == 0) __builtin_trap();
    if ((leanos_syscall(ECHO_SYS_FETCH, (uint64_t)echo_frame, 0, 0) & ECHO_REFUSED) == 0)
        __builtin_trap();
    uint64_t mac = echo_receive(ECHO_LEASE_ENDPOINT, &ip);
    if (mac >> 48 != 0 || ip >> 32 != 0) __builtin_trap();
    for (;;) {
        uint64_t seq = 0;
        uint64_t len = echo_receive(ECHO_FRAME_ENDPOINT, &seq);
        /* Records reach this subject in order, without a gap, from the
           first one after the hand-off. */
        if (last_seq != 0 && seq != last_seq + 1) __builtin_trap();
        last_seq = seq;
        if (leanos_syscall(ECHO_SYS_FETCH, (uint64_t)echo_frame, 0, 0) != len)
            __builtin_trap();
        uint64_t reply = leanos_net_reply(0, len, mac, ip);
        if (reply != 0 &&
            leanos_syscall(ECHO_SYS_SEND, (uint64_t)echo_frame, reply, 0) != 0)
            __builtin_trap();
    }
}
