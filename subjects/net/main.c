/* Network subject (issue #450), built from subjects/template and linked as
   subject C of the network-subject image (docs/network-subject.md).

   The subject answers ARP, ICMP echo and UDP echo (port 7) for one IPv4
   host. The protocol logic is not written here: it is
   `leanos_net_reply`, the C the Lean compiler generates for
   LeanOS.Net.Echo.reply (LeanOS/Net/EchoC.lean), which the build rule
   passes in as NetEcho.c and this file includes, so the three hooks it
   calls are inlined over the subject's own frame buffer.

   The subject holds no device capability: the WiFi driver subject (A)
   does. It holds the frame endpoint instead (LeanOS.NetworkSubject). Its
   loop:

     receive on endpoint 12 (7)     the driver subject sends a frame's
                                    length (RAX) and sequence number (RBX)
     fetch the frame (64)           the kernel copies the pending frame into
                                    net_frame after checking that the whole
                                    range lies in this subject's own page,
                                    and returns its length
     compute the reply in place
     send the reply (65)            the kernel copies it out under the same
                                    check; skipped when there is nothing to
                                    answer

   The first frame is the 10-byte host configuration record (a length below
   14 is never an Ethernet frame): the hardware address and IPv4 address to
   answer for. Before its first receive the subject asks to invoke the device
   once; the kernel refuses it (it holds no device capability). */
#include <leanos/subject.h>

#define NET_ENDPOINT 12u
#define NET_SYS_DEVICE 60u
#define NET_SYS_FETCH 64u
#define NET_SYS_SEND 65u
#define NET_FRAME_BUFFER 1536u
#define NET_CONFIG_BYTES 10u
/* A refused request: bit 63 and the reason. */
#define NET_REFUSED (UINT64_C(1) << 63)

#ifdef NET_EXTERNAL_FRAME
/* The Qotom lab build (scripts/build-qotom-recovery-lab.py
   --network-subject): the buffer is the bottom of the subject's stack range,
   the pages the lab's bounded copy roots alias, and the subject keeps no
   other static data. */
extern uint8_t NET_EXTERNAL_FRAME[];
#define net_frame NET_EXTERNAL_FRAME
#else
/* In the subject's stack page above the stack (bss). */
static uint8_t net_frame[NET_FRAME_BUFFER] __attribute__((aligned(16)));
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
    return off < NET_FRAME_BUFFER ? net_frame[off] : 0;
}

uint64_t net_gen_wr8(uint64_t t, uint32_t off, uint32_t v) {
    (void)t;
    if (off < NET_FRAME_BUFFER) net_frame[off] = (uint8_t)v;
    return 0;
}

#include "NetEcho.c"

/* Block on endpoint 12; the kernel wakes the subject with the two payload
   words in RAX and RBX and the delivery flag in RCX. */
static uint64_t net_receive(uint64_t *seq) {
    uint64_t rax = LEANOS_SYS_RECEIVE, rbx = 0, rcx = 0, rdx = NET_ENDPOINT;
    __asm__ volatile ("int $0x80"
                      : "+a"(rax), "+b"(rbx), "+c"(rcx), "+d"(rdx)
                      :
                      : "memory");
    if (rcx != 1) __builtin_trap();
    *seq = rbx;
    return rax;
}

static uint64_t net_be(unsigned first, unsigned count) {
    uint64_t v = 0;
    for (unsigned i = 0; i < count; ++i) v = v << 8 | net_frame[first + i];
    return v;
}

void subject_main(void) {
    uint64_t expected_seq = 1, net_mac = 0, net_ip = 0;
    if (leanos_syscall(NET_SYS_DEVICE, 0, 0, 0) == 0) __builtin_trap();
    for (;;) {
        uint64_t seq = 0;
        uint64_t len = net_receive(&seq);
        if (seq != expected_seq) __builtin_trap();
        ++expected_seq;
        if (leanos_syscall(NET_SYS_FETCH, (uint64_t)net_frame, 0, 0) != len)
            __builtin_trap();
        if (len == NET_CONFIG_BYTES) {
            net_mac = net_be(0, 6);
            net_ip = net_be(6, 4);
            continue;
        }
        uint64_t reply = leanos_net_reply(0, len, net_mac, net_ip);
        if (reply != 0 &&
            leanos_syscall(NET_SYS_SEND, (uint64_t)net_frame, reply, 0) != 0)
            __builtin_trap();
    }
}
