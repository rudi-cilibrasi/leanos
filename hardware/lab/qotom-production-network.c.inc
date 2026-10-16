/* Qotom production network profile (issue #569; docs/qotom-production.md).
 * Built by scripts/build-qotom-production.py (build-qotom-recovery-lab.py
 * --production-network) on top of the audited blocking-IPC profile.
 *
 * After the fixed first exchange, three ring-3 subjects run, each in its own
 * address space, with the roles of the q35 frame-window image
 * (LeanOS.DhcpSubject, LeanOS.FrameCopyWindow):
 *
 *   B (2)  the WiFi driver subject, the model's subject 1: it holds the
 *          device capability for the bound BCM43224 program, assigned
 *          through the reviewed variant of the PCI trust contract
 *          (qotom-broadcom-assign.c.inc, ADR 0027), and no frame port;
 *   A (1)  the DHCP subject, the model's subject 2 (subjects/dhcp with the
 *          generated client), holding a frame port whose window is A's two
 *          stack pages;
 *   C (3)  the echo subject, the model's subject 3 (subjects/echo with the
 *          generated responder), holding a frame port whose window is C's
 *          stack page.  Its address space is the boot plan's third root:
 *          the image's boot object is assembled with the three-subject page
 *          tables, so C's pages are user pages in root C only and absent
 *          from A's and B's roots, and the generated boot page plan covers
 *          all three roots; the kernel checks root C against that plan.
 *
 * Frames cross through copy windows (include/frame_copy_window.h): for each
 * port holder a fetch root and a send root built from A's boot root, which
 * map no user frame except supervisor no-execute aliases of that holder's
 * own window at the alias slots (B's text and stack pages, which A's root
 * does not map).  Every copy is decided by the generated port witness
 * leanos_frame_port_check and takes its alias address from the generated
 * operand leanos_frame_window_operand; frame_window_transfer moves the
 * whole frame under the window root and reselects the closed root.  Every
 * device request is checked against leanos_device_authorize and every
 * exchange on endpoints 12 and 13 against leanos_blocking_ipc_event.
 *
 * No recovery-lab harness: no watchdog is armed or reloaded, and FINAL is
 * followed by an absorbing halt, not a reset. */
#include "../../include/frame_copy_window.h"

/* The absorbing terminal after FINAL; tests/qotom-production-network-host.c
   replaces it to observe the record. */
#ifndef QOTOM_PROD_HALT
#define QOTOM_PROD_HALT() for (;;) __asm__ volatile("cli; hlt")
#endif

#define QOTOM_PROD_A_SUBJECT 1u
#define QOTOM_PROD_B_SUBJECT 2u
#define QOTOM_PROD_C_SUBJECT 3u
#define QOTOM_PROD_MODEL_DRIVER 1u
#define QOTOM_PROD_MODEL_DHCP 2u
#define QOTOM_PROD_MODEL_ECHO 3u
#define QOTOM_PROD_FRAME_ENDPOINT 12u
#define QOTOM_PROD_LEASE_ENDPOINT 13u
#define QOTOM_PROD_RX_AT 0x3E000u
#define QOTOM_PROD_TX_AT 0x3E800u
#define QOTOM_PROD_TX_LEN_AT 0x3F000u
#define QOTOM_PROD_LINK_BYTES 6u
#define QOTOM_PROD_TICK_BYTES 1u
#define QOTOM_PROD_FRAME_MIN 14u
#define QOTOM_PROD_FRAME_MAX 1514u
#define QOTOM_PROD_REFUSED (UINT64_C(1) << 63)
#define QOTOM_PROD_A_WINDOW_BYTES 8192u
#define QOTOM_PROD_C_WINDOW_BYTES 4096u
#define QOTOM_PROD_OP_FETCH 1u
#define QOTOM_PROD_OP_SEND 2u
#define QOTOM_PROD_MODEL_SENDER 1u
#define QOTOM_PROD_MODEL_RECEIVER 2u

/* Phases: who runs, and why. */
#define QOTOM_PROD_C_FRESH 0u      /* C from its entry, until it waits for the lease */
#define QOTOM_PROD_A_FRESH 1u      /* A after its first-exchange send, until it waits */
#define QOTOM_PROD_B_DRIVES 2u     /* B asks the driver program for records */
#define QOTOM_PROD_A_SERVES 3u     /* A woken with a record */
#define QOTOM_PROD_C_SERVES 4u     /* C woken with a record */
#define QOTOM_PROD_C_LEASED 5u     /* C woken with the lease */
#define QOTOM_PROD_A_HANDED 6u     /* A resumed after its hand-off */

extern char qotom_echo_subject_entry[];
/* The executor scratch (hardware/wifi/wifi-exec.h, spliced after this file). */
static uint8_t *qotom_net_scratch(void);

extern uint64_t page_map_level_4_c[], page_directory_pointer_c[];
extern uint64_t page_directory_c[], page_table_c[];
static struct qotom_root_pages qotom_window_closed;
static struct qotom_root_pages qotom_window_fetch_a, qotom_window_send_a;
static struct qotom_root_pages qotom_window_fetch_c, qotom_window_send_c;
static struct qotom_root_build_result qotom_window_first;
static struct frame_window qotom_windows[2];
static uint64_t qotom_saved_c[20];

static unsigned qotom_prod_phase;
static uint64_t qotom_prod_route = QOTOM_PROD_MODEL_DHCP;
static uint64_t qotom_prod_seq, qotom_prod_rx_len, qotom_prod_rx_pending;
static uint64_t qotom_prod_tx_pending, qotom_prod_tx_len, qotom_prod_sent_len;
static uint64_t qotom_prod_fetches, qotom_prod_sends, qotom_prod_refusals;
static uint64_t qotom_prod_window_copies, qotom_prod_ended;
static uint64_t qotom_prod_lease_mac, qotom_prod_lease_ip, qotom_prod_handoff_seq;
static uint64_t qotom_prod_dhcp_records, qotom_prod_echo_records;
static uint64_t qotom_prod_cycle_a12, qotom_prod_cycle_c13, qotom_prod_cycle_c12;
static uint64_t qotom_prod_ipc_edges;
static unsigned qotom_prod_a_waiting, qotom_prod_c_waiting_lease, qotom_prod_c_waiting;
static const uint64_t qotom_prod_ipc_words[4] = {
    0x0000000100010101ull, 0x0000000100010202ull,
    0x0000000200020303ull, 0x0001000200020404ull,
};
static const char *const qotom_prod_reasons[] = {
    "none", "not-holder", "not-own-window", "not-routed", "endpoint-state",
    "frame-length", "outside-window", "unknown-operation"
};

/* The model subject a Qotom subject plays. */
static uint64_t qotom_prod_model(uint64_t subject) {
    return subject == QOTOM_PROD_B_SUBJECT ? QOTOM_PROD_MODEL_DRIVER :
        subject == QOTOM_PROD_A_SUBJECT ? QOTOM_PROD_MODEL_DHCP :
        subject == QOTOM_PROD_C_SUBJECT ? QOTOM_PROD_MODEL_ECHO : 0;
}

/* The port holder's window (by model subject), or 0. */
static const struct frame_window *qotom_prod_window(uint64_t model) {
    return model == QOTOM_PROD_MODEL_DHCP ? &qotom_windows[0] :
        model == QOTOM_PROD_MODEL_ECHO ? &qotom_windows[1] : 0;
}

static uint64_t qotom_prod_request(uint64_t op, uint64_t pending, uint64_t route,
                                   uint64_t owner) {
    return op | pending << 8 | (route & 0xffu) << 16 | (owner & 0xffu) << 24;
}

static uint64_t qotom_prod_root_c_address(void) {
    return (uint64_t)page_map_level_4_c;
}

/* Root C is the boot plan's third root, unchanged: its four-level hierarchy
   is the boot shape, and every leaf equals the generated boot page plan's
   (LeanOS.BootPageTablePlan, emitted for this linked image), ignoring
   Accessed/Dirty.  In particular C's text is user read-only executable, C's
   stack user writable no-execute, and no user page of A or B is mapped. */
static __attribute__((noinline)) int qotom_prod_root_c_exact(void) {
    const struct qotom_root_pages *root = (const struct qotom_root_pages *)page_map_level_4_c;
    if ((const uint64_t *)root->pdpt != page_directory_pointer_c ||
        (const uint64_t *)root->pd != page_directory_c ||
        (const uint64_t *)root->pt != page_table_c ||
        !qotom_root_source_ancestors(root))
        return 0;
    for (size_t page = 0; page < QOTOM_ROOT_LEAVES; ++page)
        if ((root->pt[page] & ~(QOTOM_ROOT_ACCESSED | QOTOM_ROOT_DIRTY)) != leanos_boot_plan_c[page])
            return 0;
    uint64_t text = (uint64_t)__user_c_text_start >> 12, stack = (uint64_t)__user_c_stack_start >> 12;
    return leanos_boot_plan_c[text] == ((text << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_USER) &&
        leanos_boot_plan_c[stack] == ((stack << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_WRITABLE |
            QOTOM_ROOT_USER | QOTOM_ROOT_NX) &&
        leanos_boot_plan_a[text] == 0 && leanos_boot_plan_a[stack] == 0 &&
        leanos_boot_plan_b[text] == 0 && leanos_boot_plan_b[stack] == 0;
}

static __attribute__((noinline)) void qotom_prod_check_root_c(void) {
    if ((uint64_t)__user_c_text_end - (uint64_t)__user_c_text_start > 4096u ||
        (uint64_t)__user_c_stack_end - (uint64_t)__user_c_stack_start != QOTOM_PROD_C_WINDOW_BYTES ||
        !qotom_prod_root_c_exact())
        pre_admission_fail("qotom-production-root-c");
}

/* Both windows' roots, from A's boot root, checked leaf by leaf; the scratch
   closed root they are built over must equal the published closed root. */
static __attribute__((noinline)) int qotom_prod_windows_exact(void) {
    for (size_t page = 0; page < QOTOM_ROOT_LEAVES; ++page)
        if ((qotom_window_closed.pt[page] & ~(QOTOM_ROOT_ACCESSED | QOTOM_ROOT_DIRTY)) !=
            (qotom_closed_root.pt[page] & ~(QOTOM_ROOT_ACCESSED | QOTOM_ROOT_DIRTY)))
            return 0;
    for (unsigned i = 0; i < 2; ++i)
        for (int writable = 0; writable <= 1; ++writable)
            if (!frame_window_root_exact(writable ? qotom_windows[i].fetch : qotom_windows[i].send,
                    &qotom_window_closed, qotom_protected_frames,
                    qotom_root_result.protected_count, &qotom_windows[i], writable))
                return 0;
    return 1;
}

static __attribute__((noinline)) void qotom_prod_build_windows(void) {
    const struct qotom_root_pages *source = (const struct qotom_root_pages *)page_map_level_4_a;
    const uint64_t slot = (uint64_t)__user_b_text_start >> 12;
    /* A's window spans two pages, so its aliases take B's text page and the
       page after it, B's stack: both absent from A's root. */
    if ((uint64_t)__user_b_stack_start != (uint64_t)__user_b_text_start + 4096u ||
        (uint64_t)__user_b_stack_end != (uint64_t)__user_b_stack_start + 4096u ||
        (uint64_t)__user_a_stack_end - (uint64_t)__user_a_stack_start != QOTOM_PROD_A_WINDOW_BYTES)
        pre_admission_fail("qotom-production-window-slots");
    qotom_windows[0] = (struct frame_window){ &qotom_window_fetch_a, &qotom_window_send_a,
        (uint64_t)__user_a_stack_start, (uint64_t)__user_a_stack_end, slot };
    qotom_windows[1] = (struct frame_window){ &qotom_window_fetch_c, &qotom_window_send_c,
        (uint64_t)__user_c_stack_start, (uint64_t)__user_c_stack_end, slot };
    const struct qotom_root_pages *storage[] = { &qotom_window_closed, &qotom_window_fetch_a,
        &qotom_window_send_a, &qotom_window_fetch_c, &qotom_window_send_c };
    for (unsigned i = 0; i < sizeof storage / sizeof storage[0]; ++i)
        if (!qotom_root_storage_mapped(source, storage[i]))
            pre_admission_fail("qotom-production-window-storage");
    int built = 0;
    for (unsigned i = 0; i < 2; ++i)
        if (frame_window_build(source, &qotom_window_closed, qotom_protected_frames,
                qotom_root_result.protected_count, &qotom_windows[i], &qotom_window_first,
                &built) != FRAME_WINDOW_OK)
            pre_admission_fail("qotom-production-window-build");
    if (qotom_window_first.protected_count != qotom_root_result.protected_count ||
        qotom_window_first.removed_aliases != qotom_root_result.removed_aliases ||
        qotom_window_first.retained_present != qotom_root_result.retained_present ||
        !qotom_prod_windows_exact())
        pre_admission_fail("qotom-production-window-roots");
    /* The generated operand agrees with the port witness for every subject
       and route, at a window's first byte and 100 bytes in. */
    for (uint64_t model = 1; model <= 3; ++model) {
        const struct frame_window *w = qotom_prod_window(model);
        uint64_t base = w ? w->base : 0, limit = w ? w->limit : 0, s = w ? w->slot : 0;
        for (uint64_t route = QOTOM_PROD_MODEL_DHCP; route <= QOTOM_PROD_MODEL_ECHO; ++route) {
            for (uint64_t offset = 0; offset <= 100; offset += 100) {
                uint64_t request = qotom_prod_request(QOTOM_PROD_OP_FETCH, 1, route, model);
                uint64_t port = leanos_frame_port_check(model, request, base + offset,
                    QOTOM_PROD_LINK_BYTES, base, limit);
                uint64_t operand = leanos_frame_window_operand(s, request, base + offset,
                    QOTOM_PROD_LINK_BYTES, base, limit);
                uint64_t accept = w != 0 && route == model;
                if ((port == 0) != accept || (operand != 0) != accept ||
                    (operand != 0 && operand != (slot << 12) + offset))
                    pre_admission_fail("qotom-production-window-operand");
            }
        }
    }
    serial_puts("LEANOS-LAB/1 PRODUCTION-WINDOWS profile=qotom-network-v1 holders=1,3 a-window-pages=2 c-window-pages=1 fetch-root=writable send-root=read-only protected=");
    serial_u64(qotom_window_first.protected_count);
    serial_puts(" roots=5 scan=exact operand=agree root-c=exact\n");
}

/* The receiver's wake edge is taken when it next enters the kernel. */
static void qotom_prod_edge(uint64_t *cycle, uint64_t role) {
    if (leanos_blocking_ipc_event(*cycle, *cycle + 1, role) != qotom_prod_ipc_words[*cycle])
        qotom_blocking_fail("qotom-production-ipc-model");
    *cycle = (*cycle + 1) & 3u;
    qotom_prod_ipc_edges++;
}

static void qotom_prod_wake_edges(void) {
    if (current_subject == QOTOM_PROD_A_SUBJECT && qotom_prod_cycle_a12 == 3)
        qotom_prod_edge(&qotom_prod_cycle_a12, QOTOM_PROD_MODEL_RECEIVER);
    if (current_subject == QOTOM_PROD_C_SUBJECT && qotom_prod_cycle_c13 == 3)
        qotom_prod_edge(&qotom_prod_cycle_c13, QOTOM_PROD_MODEL_RECEIVER);
    if (current_subject == QOTOM_PROD_C_SUBJECT && qotom_prod_cycle_c12 == 3)
        qotom_prod_edge(&qotom_prod_cycle_c12, QOTOM_PROD_MODEL_RECEIVER);
}

static uint64_t qotom_prod_root(uint64_t subject) {
    return subject == QOTOM_PROD_A_SUBJECT ? (uint64_t)page_map_level_4_a :
        subject == QOTOM_PROD_B_SUBJECT ? (uint64_t)page_map_level_4_b :
        subject == QOTOM_PROD_C_SUBJECT ? (uint64_t)page_map_level_4_c : 0;
}

static uint64_t *qotom_prod_bank(uint64_t subject) {
    return subject == QOTOM_PROD_A_SUBJECT ? qotom_saved_a :
        subject == QOTOM_PROD_B_SUBJECT ? qotom_saved_b : qotom_saved_c;
}

/* Save the caller's continuation, restore `next`'s, and select its root. */
static uint64_t qotom_prod_switch(uint64_t *saved, uint64_t next) {
    qotom_copy_frame(qotom_prod_bank(current_subject), saved);
    qotom_copy_frame(saved, qotom_prod_bank(next));
    current_subject = next;
    qotom_entry_subject_root = qotom_prod_root(next);
    return qotom_entry_subject_root;
}

static uint64_t qotom_prod_refuse(const char *operation, uint64_t reason) {
    if (reason == 0 || reason >= sizeof qotom_prod_reasons / sizeof qotom_prod_reasons[0])
        qotom_blocking_fail("qotom-production-refusal-reason");
    qotom_prod_refusals++;
    serial_puts("LEANOS-LAB/1 NET event=refuse subject=");
    serial_u64(current_subject);
    serial_puts(" op="); serial_puts(operation);
    serial_puts(" reason="); serial_puts(qotom_prod_reasons[reason]);
    serial_puts(" model=refused\n");
    return QOTOM_PROD_REFUSED | reason;
}

/* A frame copy (64 fetch, 65 send): the port witness decides, the operand
   gives the alias address, the window root carries the frame. */
static __attribute__((noinline)) uint64_t qotom_prod_copy(uint64_t *saved, uint64_t number) {
    const uint64_t model = qotom_prod_model(current_subject);
    const struct frame_window *w = qotom_prod_window(model);
    const uint64_t fetch = number == 64;
    const uint64_t op = fetch ? QOTOM_PROD_OP_FETCH : QOTOM_PROD_OP_SEND;
    uint64_t address = saved[13], length = fetch ? qotom_prod_rx_len : saved[12];
    uint64_t pending = fetch ? qotom_prod_rx_pending : qotom_prod_tx_pending;
    uint64_t base = w ? w->base : 0, limit = w ? w->limit : 0;
    uint64_t request = qotom_prod_request(op, pending, qotom_prod_route, model);
    uint64_t witness = leanos_frame_port_check(model, request, address, length, base, limit);
    uint64_t operand = leanos_frame_window_operand(w ? w->slot : 0, request, address, length,
        base, limit);
    if ((operand != 0) != (witness == 0)) qotom_blocking_fail("qotom-production-operand");
    if (witness != 0) return qotom_prod_refuse(fetch ? "fetch" : "send", witness);
    if (!(model == QOTOM_PROD_MODEL_DHCP && qotom_prod_phase == QOTOM_PROD_A_SERVES) &&
        !(model == QOTOM_PROD_MODEL_ECHO && qotom_prod_phase == QOTOM_PROD_C_SERVES))
        qotom_blocking_fail("qotom-production-copy-sequence");
    uint64_t moved = fetch
        ? frame_window_transfer(qotom_entry_closed_root, (uint64_t)w->fetch->pml4, operand,
              (uint64_t)(qotom_net_scratch() + QOTOM_PROD_RX_AT), length)
        : frame_window_transfer(qotom_entry_closed_root, (uint64_t)w->send->pml4,
              (uint64_t)(qotom_net_scratch() + QOTOM_PROD_TX_AT), operand, length);
    if (moved != length) qotom_blocking_fail("qotom-production-transfer");
    qotom_prod_window_copies++;
    if (fetch) {
        qotom_prod_rx_pending = 0;
        qotom_prod_fetches++;
    } else {
        *(volatile uint32_t *)(qotom_net_scratch() + QOTOM_PROD_TX_LEN_AT) = (uint32_t)length;
        qotom_prod_tx_pending = 1;
        qotom_prod_tx_len = length;
        qotom_prod_sent_len = length;
        qotom_prod_sends++;
    }
    serial_puts(fetch ? "LEANOS-LAB/1 NET event=fetch subject=" : "LEANOS-LAB/1 NET event=send subject=");
    serial_u64(current_subject);
    serial_puts(" frame="); serial_u64(qotom_prod_seq);
    serial_puts(" bytes="); serial_u64(length);
    serial_puts(fetch ? " copy=fetch-root model=accepted\n" : " copy=send-root model=accepted\n");
    return fetch ? length : 0;
}

/* B's next record: hand the pending frame to the program, resume it until
   it yields the next record (or halts). */
static __attribute__((noinline)) uint64_t qotom_prod_next_record(void) {
    if (qotom_prod_ended) return 0;
    if (qotom_prod_rx_pending) qotom_blocking_fail("qotom-production-record-unfetched");
    volatile uint32_t *tx_len = (volatile uint32_t *)(qotom_net_scratch() + QOTOM_PROD_TX_LEN_AT);
    if (*tx_len != (qotom_prod_tx_pending ? qotom_prod_tx_len : 0))
        qotom_blocking_fail("qotom-production-transmit-slot");
    qotom_prod_tx_pending = 0;
    uint64_t code = lab_stream_next_key();
    if (*tx_len != 0) qotom_blocking_fail("qotom-production-transmit-not-taken");
    if (code == 0) {
        qotom_prod_ended = 1;
        return 0;
    }
    if (qotom_prod_seq == 0 ? code != QOTOM_PROD_LINK_BYTES
        : code != QOTOM_PROD_TICK_BYTES &&
          (code < QOTOM_PROD_FRAME_MIN || code > QOTOM_PROD_FRAME_MAX))
        qotom_blocking_fail("qotom-production-record-length");
    qotom_prod_rx_len = code;
    qotom_prod_rx_pending = 1;
    qotom_prod_sent_len = 0;
    ++qotom_prod_seq;
    serial_puts("LEANOS-LAB/1 NET event=deliver frame=");
    serial_u64(qotom_prod_seq);
    serial_puts(" bytes="); serial_u64(code);
    serial_puts(qotom_prod_route == QOTOM_PROD_MODEL_DHCP ? " port=dhcp\n" : " port=echo\n");
    return qotom_prod_seq << 32 | code;
}

static void qotom_prod_initial_c_frame(uint64_t *saved) {
    for (unsigned i = 0; i < 20; ++i) saved[i] = 0;
    saved[15] = (uint64_t)qotom_echo_subject_entry;
    saved[16] = UINT64_C(0x23);
    saved[17] = UINT64_C(2);
    saved[18] = (uint64_t)user_c_stack_top;
    saved[19] = UINT64_C(0x1b);
}

static void qotom_prod_print_ip(uint64_t ip) {
    serial_u64(ip >> 24 & 0xffu); serial_putc('.');
    serial_u64(ip >> 16 & 0xffu); serial_putc('.');
    serial_u64(ip >> 8 & 0xffu); serial_putc('.');
    serial_u64(ip & 0xffu);
}

/* The first continuation after B's report of the fixed exchange: A's send
   and B's report return later; C starts fresh at the echo subject's entry. */
static __attribute__((noinline)) uint64_t qotom_prod_begin(uint64_t *saved) {
    qotom_copy_frame(qotom_saved_b, saved);
    qotom_saved_b[14] = 0;
    qotom_saved_b[17] &= ~((UINT64_C(1) << 10) | (UINT64_C(1) << 18));
    qotom_saved_a[14] = 0;
    qotom_saved_a[17] &= ~((UINT64_C(1) << 10) | (UINT64_C(1) << 18));
    qotom_prod_initial_c_frame(saved);
    qotom_blocking_step = 30;
    qotom_prod_phase = QOTOM_PROD_C_FRESH;
    current_subject = QOTOM_PROD_C_SUBJECT;
    qotom_entry_subject_root = (uint64_t)page_map_level_4_c;
    serial_puts(LEANOS_SERIAL_10_IPC " event=dispatch subject=3 address-space=3 role=echo-subject context=initial\n");
    return qotom_entry_subject_root;
}

static __attribute__((noinline)) uint64_t qotom_prod_dispatch(uint64_t *saved, uint64_t number) {
    qotom_prod_wake_edges();
    const uint64_t model = qotom_prod_model(current_subject);
    if (number == 60) {
        uint64_t holder = model == QOTOM_PROD_MODEL_DRIVER;
        if (leanos_device_authorize(model, 0) != (holder ? 1u : 2u))
            qotom_blocking_fail("qotom-production-device-model");
        if (!holder) {
            qotom_prod_refusals++;
            serial_puts("LEANOS-LAB/1 NET event=refuse subject=");
            serial_u64(current_subject);
            serial_puts(" op=device-invoke reason=no-device-capability model=refused\n");
            saved[14] = QOTOM_PROD_REFUSED | 7u;
            return qotom_entry_subject_root;
        }
        if (qotom_prod_phase != QOTOM_PROD_B_DRIVES)
            qotom_blocking_fail("qotom-production-device-sequence");
        saved[14] = qotom_prod_next_record();
        return qotom_entry_subject_root;
    }
    if (number == 64 || number == 65) {
        saved[14] = qotom_prod_copy(saved, number);
        return qotom_entry_subject_root;
    }
    if (number == 8 && current_subject == QOTOM_PROD_B_SUBJECT &&
        qotom_prod_phase == QOTOM_PROD_B_DRIVES) {
        /* B's record notice goes to the routed holder, which must be
           waiting on endpoint 12. */
        unsigned to_echo = qotom_prod_route == QOTOM_PROD_MODEL_ECHO;
        if (!qotom_prod_rx_pending || saved[13] != qotom_prod_rx_len ||
            saved[12] != qotom_prod_seq ||
            (to_echo ? !qotom_prod_c_waiting : !qotom_prod_a_waiting))
            qotom_blocking_fail("qotom-production-send-record");
        uint64_t *cycle = to_echo ? &qotom_prod_cycle_c12 : &qotom_prod_cycle_a12;
        qotom_prod_edge(cycle, QOTOM_PROD_MODEL_SENDER);
        qotom_prod_edge(cycle, QOTOM_PROD_MODEL_SENDER);
        uint64_t next = to_echo ? QOTOM_PROD_C_SUBJECT : QOTOM_PROD_A_SUBJECT;
        if (to_echo) { qotom_prod_c_waiting = 0; qotom_prod_echo_records++; }
        else { qotom_prod_a_waiting = 0; qotom_prod_dhcp_records++; }
        qotom_prod_phase = to_echo ? QOTOM_PROD_C_SERVES : QOTOM_PROD_A_SERVES;
        uint64_t root = qotom_prod_switch(saved, next);
        saved[14] = qotom_prod_rx_len;
        saved[13] = qotom_prod_seq;
        saved[12] = 1;
        serial_puts(LEANOS_SERIAL_10_IPC " event=send sender=2 endpoint=12 payload0=");
        serial_u64(qotom_prod_rx_len);
        serial_puts(" payload1="); serial_u64(qotom_prod_seq);
        serial_puts(to_echo ? " receiver=3 accepted=1\n" : " receiver=1 accepted=1\n");
        return root;
    }
    if (number == 8 && current_subject == QOTOM_PROD_A_SUBJECT &&
        qotom_prod_phase == QOTOM_PROD_A_SERVES) {
        /* The hand-off: A's lease (hardware address, IPv4 address) to C,
           waiting on endpoint 13.  From now on the endpoint serves C. */
        if (saved[11] != QOTOM_PROD_LEASE_ENDPOINT || qotom_prod_route != QOTOM_PROD_MODEL_DHCP ||
            !qotom_prod_c_waiting_lease || qotom_prod_rx_pending || qotom_prod_tx_pending ||
            saved[13] >> 48 != 0 || saved[12] >> 32 != 0)
            qotom_blocking_fail("qotom-production-handoff");
        qotom_prod_edge(&qotom_prod_cycle_c13, QOTOM_PROD_MODEL_SENDER);
        qotom_prod_edge(&qotom_prod_cycle_c13, QOTOM_PROD_MODEL_SENDER);
        qotom_prod_c_waiting_lease = 0;
        qotom_prod_lease_mac = saved[13];
        qotom_prod_lease_ip = saved[12];
        qotom_prod_handoff_seq = qotom_prod_seq;
        qotom_prod_route = QOTOM_PROD_MODEL_ECHO;
        qotom_prod_phase = QOTOM_PROD_C_LEASED;
        saved[14] = 0;
        uint64_t root = qotom_prod_switch(saved, QOTOM_PROD_C_SUBJECT);
        saved[14] = qotom_prod_lease_mac;
        saved[13] = qotom_prod_lease_ip;
        saved[12] = 1;
        serial_puts("LEANOS-LAB/1 NET event=handoff from=1 to=3 frame=");
        serial_u64(qotom_prod_seq);
        serial_puts(" lease=");
        qotom_prod_print_ip(qotom_prod_lease_ip);
        serial_puts(" route=echo address-spaces=separate model=accepted\n");
        return root;
    }
    if (number == 7) {
        if (current_subject == QOTOM_PROD_C_SUBJECT && qotom_prod_phase == QOTOM_PROD_C_FRESH) {
            if (saved[11] != QOTOM_PROD_LEASE_ENDPOINT || qotom_prod_c_waiting_lease)
                qotom_blocking_fail("qotom-production-echo-lease-receive");
            qotom_prod_c_waiting_lease = 1;
            qotom_prod_edge(&qotom_prod_cycle_c13, QOTOM_PROD_MODEL_RECEIVER);
            qotom_prod_phase = QOTOM_PROD_A_FRESH;
            serial_puts(LEANOS_SERIAL_10_IPC " event=block subject=3 endpoint=13 role=echo-subject\n");
            return qotom_prod_switch(saved, QOTOM_PROD_A_SUBJECT);
        }
        if (current_subject == QOTOM_PROD_A_SUBJECT &&
            (qotom_prod_phase == QOTOM_PROD_A_FRESH || qotom_prod_phase == QOTOM_PROD_A_SERVES ||
             qotom_prod_phase == QOTOM_PROD_A_HANDED)) {
            if (saved[11] != QOTOM_PROD_FRAME_ENDPOINT || qotom_prod_a_waiting ||
                qotom_prod_rx_pending)
                qotom_blocking_fail("qotom-production-dhcp-receive");
            qotom_prod_a_waiting = 1;
            qotom_prod_edge(&qotom_prod_cycle_a12, QOTOM_PROD_MODEL_RECEIVER);
            serial_puts(qotom_prod_route == QOTOM_PROD_MODEL_DHCP
                ? LEANOS_SERIAL_10_IPC " event=block subject=1 endpoint=12 role=dhcp-subject\n"
                : LEANOS_SERIAL_10_IPC " event=block subject=1 endpoint=12 role=dhcp-subject parked=1\n");
            qotom_prod_phase = QOTOM_PROD_B_DRIVES;
            uint64_t root = qotom_prod_switch(saved, QOTOM_PROD_B_SUBJECT);
            saved[14] = 0;
            return root;
        }
        if (current_subject == QOTOM_PROD_C_SUBJECT &&
            (qotom_prod_phase == QOTOM_PROD_C_LEASED || qotom_prod_phase == QOTOM_PROD_C_SERVES)) {
            if (saved[11] != QOTOM_PROD_FRAME_ENDPOINT || qotom_prod_c_waiting ||
                qotom_prod_rx_pending || qotom_prod_route != QOTOM_PROD_MODEL_ECHO)
                qotom_blocking_fail("qotom-production-echo-receive");
            qotom_prod_c_waiting = 1;
            qotom_prod_edge(&qotom_prod_cycle_c12, QOTOM_PROD_MODEL_RECEIVER);
            serial_puts(LEANOS_SERIAL_10_IPC " event=block subject=3 endpoint=12 role=echo-subject\n");
            unsigned leased = qotom_prod_phase == QOTOM_PROD_C_LEASED;
            qotom_prod_phase = leased ? QOTOM_PROD_A_HANDED : QOTOM_PROD_B_DRIVES;
            uint64_t root = qotom_prod_switch(saved,
                leased ? QOTOM_PROD_A_SUBJECT : QOTOM_PROD_B_SUBJECT);
            saved[14] = 0;
            return root;
        }
        qotom_blocking_fail("qotom-production-receive-sequence");
    }
    if (number == 61 && current_subject == QOTOM_PROD_B_SUBJECT &&
        qotom_prod_phase == QOTOM_PROD_B_DRIVES) {
        if (!qotom_prod_ended || qotom_prod_fetches != qotom_prod_seq ||
            qotom_prod_rx_pending || qotom_prod_tx_pending ||
            qotom_prod_route != QOTOM_PROD_MODEL_ECHO || qotom_prod_handoff_seq == 0 ||
            qotom_prod_dhcp_records != qotom_prod_handoff_seq ||
            qotom_prod_echo_records != qotom_prod_seq - qotom_prod_handoff_seq ||
            !qotom_prod_a_waiting || !qotom_prod_c_waiting || qotom_prod_c_waiting_lease ||
            qotom_prod_window_copies != qotom_prod_fetches + qotom_prod_sends ||
            qotom_prod_cycle_a12 != 1 || qotom_prod_cycle_c13 != 0 || qotom_prod_cycle_c12 != 1)
            qotom_blocking_fail("qotom-production-count");
        serial_puts(LEANOS_SERIAL_10_FINAL " status=PASS profile=qotom-network-v1 subjects=3 dhcp-subject=1 echo-subject=3 device-holder=2 address-spaces=3 lease=");
        qotom_prod_print_ip(qotom_prod_lease_ip);
        serial_puts(" frames="); serial_u64(qotom_prod_seq);
        serial_puts(" dhcp-frames="); serial_u64(qotom_prod_dhcp_records);
        serial_puts(" echo-frames="); serial_u64(qotom_prod_echo_records);
        serial_puts(" fetches="); serial_u64(qotom_prod_fetches);
        serial_puts(" sends="); serial_u64(qotom_prod_sends);
        serial_puts(" refusals="); serial_u64(qotom_prod_refusals);
        serial_puts(" ipc-edges="); serial_u64(qotom_prod_ipc_edges);
        serial_puts(" window-copies="); serial_u64(qotom_prod_window_copies);
        serial_putc('\n');
        QOTOM_PROD_HALT();
    }
    qotom_blocking_fail("qotom-production-sequence");
}
