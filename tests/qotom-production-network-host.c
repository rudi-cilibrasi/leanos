/* Hosted test of the Qotom production network dispatcher (issue #569).

   hardware/lab/qotom-production-network.c.inc runs only in the production
   Qotom image, which cannot boot under QEMU. This harness compiles the same
   file against stand-ins for the kernel it is spliced into and drives its
   dispatcher through a whole session, syscall by syscall, as the three
   subjects issue them. The generated witnesses it consults are the real
   ones (leanos_frame_port_check, leanos_frame_window_operand,
   leanos_device_authorize, leanos_blocking_ipc_event).

   The stand-ins: subject memory is three host buffers at the subjects'
   linked addresses (below 16 MiB, as on the Qotom); the window transfer
   resolves an alias through the window it was given and checks the root
   it returns to; the driver program yields scripted records and checks
   every frame left for it.

   The session: C starts and waits for the lease, A starts and waits for a
   record, B's frame fetch is refused, then the link record and an OFFER
   reach A (which answers each), the ACK reaches A, A hands the lease to
   C, A parks, an ICMP request reaches C (which answers), and the program
   ends. Every refusal, root switch, payload register, window copy byte and
   the FINAL record are checked; then each step's precondition is broken
   once and the dispatcher must fail closed. */
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "boundary-abi.h"

#define LEANOS_SERIAL_10_IPC "LEANOS/10 IPC"
#define LEANOS_SERIAL_10_FINAL "LEANOS/10 FINAL"

/* The subjects' linked layout, as the production image links it. */
#define A_STACK 0x3b8000u
#define A_STACK_END 0x3ba000u
#define B_TEXT 0x3ba000u
#define B_TEXT_END 0x3ba3f3u
#define B_STACK 0x3bb000u
#define B_STACK_END 0x3bc000u
#define C_TEXT 0x3bc000u
#define C_TEXT_END 0x3bc5a0u
#define C_STACK 0x3bd000u
#define C_STACK_END 0x3be000u
#define __user_a_stack_start ((char *)(uintptr_t)A_STACK)
#define __user_a_stack_end ((char *)(uintptr_t)A_STACK_END)
#define __user_b_text_start ((char *)(uintptr_t)B_TEXT)
#define __user_b_stack_start ((char *)(uintptr_t)B_STACK)
#define __user_b_stack_end ((char *)(uintptr_t)B_STACK_END)
#define __user_c_text_start ((char *)(uintptr_t)C_TEXT)
#define __user_c_text_end ((char *)(uintptr_t)C_TEXT_END)
#define __user_c_stack_start ((char *)(uintptr_t)C_STACK)
#define __user_c_stack_end ((char *)(uintptr_t)C_STACK_END)
#define user_c_stack_top ((char *)(uintptr_t)C_STACK_END)
#define CLOSED_ROOT 0x300000u

static jmp_buf failed;
static const char *failure;
static int halted;
static char final_record[512];
static size_t final_length;
static int capturing;

static void serial_putc(char c) {
    if (capturing && final_length + 1 < sizeof final_record) final_record[final_length++] = c;
}
static void serial_puts(const char *s) {
    if (strncmp(s, LEANOS_SERIAL_10_FINAL, strlen(LEANOS_SERIAL_10_FINAL)) == 0) capturing = 1;
    for (; *s; ++s) serial_putc(*s);
}
static void serial_u64(uint64_t v) {
    char digits[21];
    int n = 0;
    do digits[n++] = (char)('0' + v % 10); while ((v /= 10) != 0);
    while (n) serial_putc(digits[--n]);
}
static __attribute__((noreturn)) void pre_admission_fail(const char *reason) {
    failure = reason;
    longjmp(failed, 1);
}
static __attribute__((noreturn)) void qotom_blocking_fail(const char *reason) {
    pre_admission_fail(reason);
}
#define QOTOM_PROD_HALT() do { halted = 1; longjmp(failed, 2); } while (0)

/* The kernel state the dispatcher shares with the blocking-IPC profile. */
static uint64_t current_subject, qotom_blocking_step, qotom_entry_subject_root;
static uint64_t qotom_entry_closed_root = CLOSED_ROOT;
static uint64_t qotom_saved_a[20], qotom_saved_b[20];
static void qotom_copy_frame(uint64_t *destination, const uint64_t *source) {
    memcpy(destination, source, 20 * sizeof *destination);
}
static uint64_t page_map_level_4_a[512], page_map_level_4_b[512];
uint64_t page_map_level_4_c[512], page_directory_pointer_c[512];
uint64_t page_directory_c[512], page_table_c[4096];
char qotom_echo_subject_entry[16];
static const unsigned long long leanos_boot_plan_a[4096], leanos_boot_plan_b[4096],
    leanos_boot_plan_c[4096];
#include "../include/qotom_copy_root_builder.h"
static struct qotom_root_pages qotom_closed_root;
static uint64_t qotom_protected_frames[QOTOM_ROOT_MAX_PROTECTED];
static struct qotom_root_build_result qotom_root_result;
static int qotom_root_storage_mapped(const struct qotom_root_pages *source,
                                     const struct qotom_root_pages *storage) {
    (void)source; (void)storage;
    return 1;
}

/* Simulated subject memory at the linked addresses. */
static uint8_t memory_a[A_STACK_END - A_STACK], memory_c[C_STACK_END - C_STACK];
static uint8_t scratch[0x40000];
static uint8_t *qotom_net_scratch(void) { return scratch; }
static uint8_t *subject_byte(uint64_t address) {
    if (address >= A_STACK && address < A_STACK_END) return &memory_a[address - A_STACK];
    if (address >= C_STACK && address < C_STACK_END) return &memory_c[address - C_STACK];
    return 0;
}

static uint64_t window_copies;
uint64_t frame_window_transfer(uint64_t resume_root, uint64_t window_root,
    uint64_t destination, uint64_t source, uint64_t length);

/* The driver program: scripted records, and a check of every frame left
   for it in the transmit slot. */
#define RECORDS 4u
static const uint64_t record_lengths[RECORDS] = { 6, 342, 342, 98 };
static const uint64_t expected_sent[RECORDS] = { 342, 342, 0, 98 };
static unsigned yielded;
static uint64_t transmitted;
static uint64_t lab_stream_next_key(void);

#include "../hardware/lab/qotom-production-network.c.inc"

uint64_t frame_window_transfer(uint64_t resume_root, uint64_t window_root,
    uint64_t destination, uint64_t source, uint64_t length) {
    if (resume_root != CLOSED_ROOT || length > FRAME_WINDOW_MAX_BYTES) abort();
    for (unsigned i = 0; i < 2; ++i) {
        const struct frame_window *w = &qotom_windows[i];
        int fetch = window_root == (uint64_t)w->fetch->pml4;
        if (!fetch && window_root != (uint64_t)w->send->pml4) continue;
        uint64_t alias = fetch ? destination : source;
        uint64_t first = w->slot << 12, past = first + (w->limit - w->base);
        if (alias < first || alias + length > past) abort();
        for (uint64_t k = 0; k < length; ++k) {
            uint8_t *user = subject_byte(w->base + (alias - first) + k);
            if (!user) abort();
            if (fetch) *user = ((const uint8_t *)(uintptr_t)source)[k];
            else ((uint8_t *)(uintptr_t)destination)[k] = *user;
        }
        ++window_copies;
        return length;
    }
    abort();
}

static uint64_t lab_stream_next_key(void) {
    volatile uint32_t *tx_len = (volatile uint32_t *)(scratch + QOTOM_PROD_TX_AT + 0x800u);
    /* The lease signal is set by the hand-off, which follows the third
       record (the ACK), and never before. */
    if (*(volatile uint32_t *)(scratch + QOTOM_PROD_LEASE_SIGNAL_AT) != (yielded >= 3 ? 1u : 0u))
        abort();
    if (yielded > 0) {
        uint64_t want = expected_sent[yielded - 1];
        if (*tx_len != want) abort();
        for (uint64_t k = 0; k < want; ++k)
            if (scratch[QOTOM_PROD_TX_AT + k] != (uint8_t)(0xa0u + yielded + k)) abort();
        if (want) ++transmitted;
        *tx_len = 0;
    }
    if (yielded == RECORDS) return 0;
    uint64_t length = record_lengths[yielded++];
    for (uint64_t k = 0; k < length; ++k)
        scratch[QOTOM_PROD_RX_AT + k] = (uint8_t)(0x10u * yielded + k);
    return length;
}

static uint64_t saved[20];
static unsigned failures, checks;
static int quiet;

static void expect(int ok, const char *what) {
    if (quiet) return;
    ++checks;
    if (!ok) {
        ++failures;
        fprintf(stderr, "FAIL %s\n", what);
    }
}

/* One syscall by the current subject: number in RAX, then RBX, RCX, RDX. */
static uint64_t call(uint64_t number, uint64_t rbx, uint64_t rcx, uint64_t rdx) {
    saved[14] = number; saved[13] = rbx; saved[12] = rcx; saved[11] = rdx;
    return qotom_prod_dispatch(saved, number);
}

static void setup(void) {
    memset(saved, 0, sizeof saved);
    memset(qotom_saved_a, 0, sizeof qotom_saved_a);
    memset(qotom_saved_b, 0, sizeof qotom_saved_b);
    memset(qotom_saved_c, 0, sizeof qotom_saved_c);
    memset(memory_a, 0, sizeof memory_a);
    memset(memory_c, 0, sizeof memory_c);
    memset(scratch, 0, sizeof scratch);
    qotom_prod_phase = 0; qotom_prod_route = QOTOM_PROD_MODEL_DHCP;
    qotom_prod_seq = qotom_prod_rx_len = qotom_prod_rx_pending = 0;
    qotom_prod_tx_pending = qotom_prod_tx_len = qotom_prod_sent_len = 0;
    qotom_prod_fetches = qotom_prod_sends = qotom_prod_refusals = 0;
    qotom_prod_window_copies = qotom_prod_ended = 0;
    qotom_prod_lease_mac = qotom_prod_lease_ip = qotom_prod_handoff_seq = 0;
    qotom_prod_dhcp_records = qotom_prod_echo_records = 0;
    qotom_prod_cycle_a12 = qotom_prod_cycle_c13 = qotom_prod_cycle_c12 = 0;
    qotom_prod_ipc_edges = 0;
    qotom_prod_a_waiting = qotom_prod_c_waiting_lease = qotom_prod_c_waiting = 0;
    yielded = 0; transmitted = 0; window_copies = 0; halted = 0;
    capturing = 0; final_length = 0; failure = 0;
    qotom_windows[0] = (struct frame_window){ &qotom_window_fetch_a, &qotom_window_send_a,
        A_STACK, A_STACK_END, B_TEXT >> 12 };
    qotom_windows[1] = (struct frame_window){ &qotom_window_fetch_c, &qotom_window_send_c,
        C_STACK, C_STACK_END, B_TEXT >> 12 };
    /* B reports the fixed first exchange; A's send returns later. */
    current_subject = 2; qotom_blocking_step = 4;
    qotom_entry_subject_root = (uint64_t)page_map_level_4_b;
    qotom_saved_a[15] = 0x3b6020u;
    saved[15] = 0x3ba040u;
}

/* The subject leaves a frame of `length` bytes at its buffer for a send. */
static void fill(uint64_t base, uint64_t length) {
    for (uint64_t k = 0; k < length; ++k) *subject_byte(base + k) = (uint8_t)(0xa0u + yielded + k);
}

#define REFUSED(reason) ((UINT64_C(1) << 63) | (reason))
static const uint64_t mac = UINT64_C(0x0013ef7a1c22), ip = UINT64_C(0x0a000210);

/* The whole session. `break_step` > 0 breaks that step's precondition. */
static int session(int break_step) {
    int step = 0;
#define STEP(cond) do { if (++step == break_step) { cond; } } while (0)
    uint64_t root = qotom_prod_begin(saved);
    expect(root == (uint64_t)page_map_level_4_c && current_subject == 3, "begin enters C");
    expect(saved[15] == (uint64_t)qotom_echo_subject_entry && saved[18] == C_STACK_END &&
           saved[16] == 0x23 && saved[19] == 0x1b, "C's initial frame");
    expect(call(60, 0, 0, 0) == (uint64_t)page_map_level_4_c && saved[14] == REFUSED(7),
           "C's device invocation is refused");
    expect(call(64, C_STACK, 0, 0) == (uint64_t)page_map_level_4_c && saved[14] == REFUSED(3),
           "C's fetch before the hand-off is not routed");
    STEP(saved[11] = 12);
    uint64_t lease_endpoint = break_step == step ? 12 : 13;
    root = call(7, 0, 0, lease_endpoint);
    expect(root == (uint64_t)page_map_level_4_a && current_subject == 1 && saved[14] == 0 &&
           saved[15] == 0x3b6020u, "C waits for the lease; A's send returns");
    expect(call(60, 0, 0, 0) == (uint64_t)page_map_level_4_a && saved[14] == REFUSED(7),
           "A's device invocation is refused");
    root = call(7, 0, 0, 12);
    expect(root == (uint64_t)page_map_level_4_b && current_subject == 2 && saved[14] == 0 &&
           saved[15] == 0x3ba040u, "A waits on endpoint 12; B's report returns");
    expect(call(64, B_STACK, 0, 0) == (uint64_t)page_map_level_4_b && saved[14] == REFUSED(1),
           "B's frame fetch is refused: no port");
    for (unsigned record = 1; record <= 3; ++record) {
        uint64_t next = call(60, 0, 0, 0);
        uint64_t got = saved[14];
        expect(next == (uint64_t)page_map_level_4_b && got == ((uint64_t)record << 32 |
               record_lengths[record - 1]), "B takes the next record");
        STEP(got = got + 1);
        root = call(8, got & 0xffffffffu, got >> 32, 0);
        expect(root == (uint64_t)page_map_level_4_a && current_subject == 1 &&
               saved[14] == record_lengths[record - 1] && saved[13] == record &&
               saved[12] == 1, "the record wakes A with its length and number");
        STEP(saved[13] = A_STACK_END);
        uint64_t buffer = break_step == step ? A_STACK_END - 2 : A_STACK;
        expect(call(64, buffer, 0, 0) == (uint64_t)page_map_level_4_a &&
               saved[14] == record_lengths[record - 1], "A fetches the record");
        int same = 1;
        for (uint64_t k = 0; k < record_lengths[record - 1]; ++k)
            same &= memory_a[k] == (uint8_t)(0x10u * record + k);
        expect(same, "the record is in A's window, exactly");
        if (record < 3) {
            fill(A_STACK, 342);
            expect(call(65, A_STACK, 342, 0) == (uint64_t)page_map_level_4_a && saved[14] == 0,
                   "A sends its DHCP frame");
            root = call(7, 0, 0, 12);
            expect(root == (uint64_t)page_map_level_4_b && current_subject == 2 &&
                   saved[14] == 0, "A waits again; B's send returns 0");
        }
    }
    STEP(qotom_prod_c_waiting_lease = 0);
    root = call(8, mac, ip, 13);
    expect(root == (uint64_t)page_map_level_4_c && current_subject == 3 && saved[14] == mac &&
           saved[13] == ip && saved[12] == 1, "the hand-off delivers the lease to C");
    root = call(7, 0, 0, 12);
    expect(root == (uint64_t)page_map_level_4_a && current_subject == 1 && saved[14] == 0,
           "C waits on endpoint 12; A's hand-off returns 0");
    expect(call(64, A_STACK, 0, 0) == (uint64_t)page_map_level_4_a && saved[14] == REFUSED(3),
           "A's fetch after the hand-off is not routed");
    root = call(7, 0, 0, 12);
    expect(root == (uint64_t)page_map_level_4_b && current_subject == 2 && saved[14] == 0,
           "A parks; B's send returns 0");
    uint64_t next = call(60, 0, 0, 0);
    uint64_t got = saved[14];
    expect(next == (uint64_t)page_map_level_4_b && got == ((uint64_t)4 << 32 | 98),
           "B takes the echo request");
    root = call(8, got & 0xffffffffu, got >> 32, 0);
    expect(root == (uint64_t)page_map_level_4_c && current_subject == 3 && saved[14] == 98 &&
           saved[13] == 4, "the request wakes C");
    expect(call(64, C_STACK, 0, 0) == (uint64_t)page_map_level_4_c && saved[14] == 98,
           "C fetches the request");
    int same = 1;
    for (uint64_t k = 0; k < 98; ++k) same &= memory_c[k] == (uint8_t)(0x40u + k);
    expect(same, "the request is in C's window, exactly");
    STEP(fill(C_STACK, 98); call(65, C_STACK, 13, 0));
    fill(C_STACK, 98);
    expect(call(65, C_STACK, 98, 0) == (uint64_t)page_map_level_4_c && saved[14] == 0,
           "C sends its reply");
    root = call(7, 0, 0, 12);
    expect(root == (uint64_t)page_map_level_4_b && current_subject == 2 && saved[14] == 0,
           "C waits again; B's send returns 0");
    expect(call(60, 0, 0, 0) == (uint64_t)page_map_level_4_b && saved[14] == 0,
           "the program ends after its last frame is taken");
    STEP(qotom_prod_c_waiting = 0);
    call(61, 0, 0, 0);
    return 0;
#undef STEP
}

int main(void) {
    setup();
    int how = setjmp(failed);
    if (how == 0) {
        session(0);
        expect(0, "the session reaches FINAL");
    } else if (how == 1) {
        fprintf(stderr, "dispatcher failed: %s\n", failure);
        expect(0, "the session completes");
    }
    expect(halted, "FINAL is followed by the halt");
    final_record[final_length] = 0;
    const char *want = LEANOS_SERIAL_10_FINAL " status=PASS profile=qotom-network-v1 subjects=3 "
        "dhcp-subject=1 echo-subject=3 device-holder=2 address-spaces=3 lease=10.0.2.16 "
        "frames=4 dhcp-frames=3 echo-frames=1 fetches=4 sends=3 refusals=5 ipc-edges=";
    expect(strncmp(final_record, want, strlen(want)) == 0, "the FINAL record");
    expect(window_copies == 7 && transmitted == 3, "every copy went through a window");
    /* Every broken precondition fails closed, never reaching FINAL. */
    quiet = 1;
    for (volatile int broken = 1; broken <= 8; ++broken) {
        setup();
        how = setjmp(failed);
        if (how == 0) session(broken);
        if (how == 0 || halted) {
            ++failures;
            fprintf(stderr, "FAIL broken step %d reached the end\n", broken);
        }
        ++checks;
    }
    quiet = 0;
    if (failures) {
        fprintf(stderr, "Qotom production dispatcher: %u of %u checks failed\n", failures, checks);
        return 1;
    }
    printf("%s", final_record);
    printf("Qotom production dispatcher: %u checks PASS\n", checks);
    return 0;
}
