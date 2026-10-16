/* Qotom network subject (issue #450; docs/wifi-driver.md, "Ring-3 network
 * subject on the Qotom").  Lab only, built by
 * scripts/build-qotom-recovery-lab.py --network-subject on top of
 * --ipc-device-stream.
 *
 * The roles of the two audited Qotom subjects after their fixed first
 * exchange are those of the q35 network-subject image with the subjects
 * renamed: B is the WiFi driver subject (the model's subject 1, holder of the
 * device capability for the bound BCM43224 program), A is the network subject
 * (the model's subject 3, holder of the frame endpoint), built from the same
 * subjects/net sources and the same generated responder as the q35 subject C.
 * A runs the network subject because the audited bounded copy roots alias
 * exactly A's two stack pages: the kernel copies a frame into A's buffer with
 * the writable copy-out root and a reply out with the read-only copy root,
 * sixteen bytes per leanos_copy_root_transfer, the primitive's audited bound.
 * No copy root, alias or transfer primitive changes.
 *
 * Every copy is checked against the generated witness leanos_frame_copy_check
 * (NetworkSubject.frameCopyCheck) with A in the model's subject 3 and A's
 * stack range as the window, every device request against
 * leanos_device_authorize with B in the model's subject 1, and every frame
 * exchange against leanos_blocking_ipc_event with B in the model's sender
 * role and A in its receiver role.  The endpoint layout in the executor
 * scratch is LeanOS.Net.FrameSource's.
 *
 * With --dhcp-subject (issue #556, LEANOS_QOTOM_DHCP_SUBJECT) the driver
 * serves the link-only endpoint (LeanOS.Wifi.Endpoint.serveLink: the 6-byte
 * link record, then frames and 1-byte ticks) and leases nothing.  A runs two
 * subjects in turn, because the audited copy roots alias only A's stack
 * pages: first the DHCP subject (subjects/dhcp, the model's subject 2), which
 * leases an address and sends it on endpoint 13; the kernel then zeroes both
 * of A's stack pages through the writable copy-out root, holds the lease, and
 * restarts A fresh at qotom_echo_subject_entry, the echo subject
 * (subjects/echo, the model's subject 3), which receives the lease on
 * endpoint 13 and answers only for it.  Every copy is checked against
 * leanos_frame_port_check (DhcpSubject.framePortCheck) with the current
 * occupant as the caller, the window's owner and the port the endpoint
 * serves.  The separation of the two subjects is in time (the scrub), not in
 * address space as on q35; the lease exchange is not checked against
 * leanos_blocking_ipc_event, because the kernel holds it across the
 * restart.
 *
 * With --long-session (issue #557, LEANOS_QOTOM_LONG_SESSION; requires
 * --dhcp-subject) the kernel reloads the TCO watchdog GRUB armed for 120
 * ticks while the driver subject makes progress: on the link record, and
 * after every 40 ticks the endpoint yields, at most
 * LEANOS_QOTOM_WATCHDOG_KICKS times, each reload decided by the generated
 * check leanos_qotom_watchdog_kick (LeanOS.QotomWatchdogKick).  The only
 * watchdog write is the reload, TCO_RLD, as FreeBSD's ichwd reloads; the
 * timeout, the halt bit, NO_REBOOT and SMI routing stay GRUB's.  Once the
 * last reload in the budget is made, the kernel ends the session before it
 * would resume the driver program again, decided by the generated check
 * leanos_qotom_watchdog_session_end (issue #567), so FINAL (with
 * session-end=budget) always comes before the budget runs out.  The safety
 * argument is in docs/wifi-driver.md, "Long sessions". */
#define QOTOM_NET_RX_AT 0x3E000u
#define QOTOM_NET_TX_AT 0x3E800u
#define QOTOM_NET_TX_LEN_AT 0x3F000u
#define QOTOM_NET_CONFIG_BYTES 10u
#define QOTOM_NET_FRAME_MIN 14u
#define QOTOM_NET_FRAME_MAX 1514u
#define QOTOM_NET_REFUSED (UINT64_C(1) << 63)
#define QOTOM_NET_MODEL_DRIVER 1u
#define QOTOM_NET_MODEL_NETWORK 3u
#define QOTOM_NET_STACK_BYTES 8192u
#ifdef LEANOS_QOTOM_DHCP_SUBJECT
#define QOTOM_NET_LINK_BYTES 6u
#define QOTOM_NET_TICK_BYTES 1u
#define QOTOM_NET_LEASE_ENDPOINT 13u
#define QOTOM_NET_MODEL_DHCP 2u
extern char qotom_echo_subject_entry[];
/* The model subject A runs as: the DHCP subject, then the echo subject. */
static uint64_t qotom_net_a_model = QOTOM_NET_MODEL_DHCP;
static uint64_t qotom_net_lease_mac, qotom_net_lease_ip, qotom_net_lease_held;
static uint64_t qotom_net_handoff_seq;
static const uint8_t qotom_net_zeros[16];
#endif

static uint64_t qotom_net_seq, qotom_net_rx_len, qotom_net_rx_pending;
static uint64_t qotom_net_tx_pending, qotom_net_tx_len;
static uint64_t qotom_net_fetches, qotom_net_replies, qotom_net_refusals;
static uint64_t qotom_net_ipc_step, qotom_net_ipc_edges;
static unsigned qotom_net_waiting, qotom_net_ended;
static const uint64_t qotom_net_ipc_words[4] = {
    0x0000000100010101ull, 0x0000000100010202ull,
    0x0000000200020303ull, 0x0001000200020404ull,
};
static struct qotom_copy_operand qotom_net_operands[16];

#ifdef LEANOS_QOTOM_LONG_SESSION
#ifndef LEANOS_QOTOM_DHCP_SUBJECT
#error "a long session needs the link-only endpoint's ticks (--dhcp-subject)"
#endif
#ifndef LEANOS_QOTOM_WATCHDOG_KICKS
#error "a long session needs its watchdog kick budget"
#endif
/* Bay Trail TCO v3 at ACPI base 0x400 + 0x60, the registers GRUB checked
   and armed (hardware/lab/grub-qotom-watchdog.cfg). */
#define QOTOM_TCO_RLD 0x460u
#define QOTOM_TCO1_CNT 0x468u
#define QOTOM_TCO_TMR 0x472u
#define QOTOM_WATCHDOG_LINK 1u
#define QOTOM_WATCHDOG_TICK 2u
static uint64_t qotom_wd_ticks, qotom_wd_kicks, qotom_wd_stopped;
/* The session ended at its kick budget (issue #567), and whether a reply
   was left unsent then. */
static uint64_t qotom_wd_budget_end, qotom_wd_unsent;

static inline uint16_t qotom_wd_in16(uint16_t port) {
    uint16_t value;
    __asm__ volatile("inw %1, %0" : "=a"(value) : "Nd"(port));
    return value;
}

/* The image's one watchdog store: reload the running countdown (TCO_RLD,
   any value; FreeBSD ichwd_tmr_reload writes 1 on TCO v2/v3).  Out of line,
   so the audit finds it and its single caller. */
static __attribute__((noinline)) void qotom_watchdog_reload(void) {
    __asm__ volatile("outw %0, %1" : : "a"((uint16_t)1), "d"((uint16_t)QOTOM_TCO_RLD));
}

/* A driver record that shows progress: the link record (the join and the
   4-way handshake are done) or a tick (one second of the radio's TSF time,
   yielded by the driver program and reaching the kernel only after the
   subject took the previous record).  Reload the timer when the generated
   check admits it; once it refuses for any reason but "not due", never
   reload again, so the board resets at most 120 seconds after the last
   reload. */
static __attribute__((noinline)) void qotom_watchdog_progress(uint64_t event) {
    if (qotom_wd_stopped) return;
    if (event == QOTOM_WATCHDOG_TICK) qotom_wd_ticks++;
    uint64_t count = qotom_wd_in16(QOTOM_TCO1_CNT);
    uint64_t timer = qotom_wd_in16(QOTOM_TCO_TMR);
    uint64_t decision = leanos_qotom_watchdog_kick(event, qotom_wd_ticks, qotom_wd_kicks,
        LEANOS_QOTOM_WATCHDOG_KICKS, count, timer);
    if (decision == 1) return;
    if (decision != 0) {
        qotom_wd_stopped = 1;
        serial_puts("LEANOS-LAB/1 WATCHDOG-KICK stopped reason=");
        serial_u64(decision);
        serial_puts(" kicks="); serial_u64(qotom_wd_kicks);
        serial_puts(" count="); serial_u64(count);
        serial_puts(" timer="); serial_u64(timer);
        serial_putc('\n');
        return;
    }
    qotom_watchdog_reload();
    qotom_wd_kicks++;
    serial_puts("LEANOS-LAB/1 WATCHDOG-KICK n=");
    serial_u64(qotom_wd_kicks);
    serial_puts(" budget="); serial_u64(LEANOS_QOTOM_WATCHDOG_KICKS);
    serial_puts(event == QOTOM_WATCHDOG_LINK ? " event=link" : " event=ticks ticks=");
    if (event == QOTOM_WATCHDOG_TICK) serial_u64(qotom_wd_ticks);
    serial_puts(" ticks-timeout=120\n");
    qotom_wd_ticks = 0;
}

/* Before the driver program is resumed for its next record (issue #567):
   once the generated check says the budget is spent, i.e. the last reload
   was just made, end the session here instead of serving on.  The serve
   window is measured in the access point's TSF time, which LeanOS does not
   control, so the window alone cannot keep the session inside its budget;
   ending here puts FINAL inside the 120 seconds the last reload gave. */
static __attribute__((noinline)) uint64_t qotom_watchdog_session_spent(void) {
    if (leanos_qotom_watchdog_session_end(qotom_wd_kicks, LEANOS_QOTOM_WATCHDOG_KICKS) == 0)
        return 0;
    serial_puts("LEANOS-LAB/1 WATCHDOG-KICK session-end reason=budget kicks=");
    serial_u64(qotom_wd_kicks);
    serial_puts(" budget="); serial_u64(LEANOS_QOTOM_WATCHDOG_KICKS);
    serial_putc('\n');
    return 1;
}
#endif
/* The executor scratch (hardware/wifi/wifi-exec.h, spliced after this file). */
static uint8_t *qotom_net_scratch(void);

static uint64_t qotom_net_model_subject(void) {
#ifdef LEANOS_QOTOM_DHCP_SUBJECT
    if (current_subject == 1) return qotom_net_a_model;
#endif
    return current_subject == 1 ? QOTOM_NET_MODEL_NETWORK :
        current_subject == 2 ? QOTOM_NET_MODEL_DRIVER : 0;
}

static void qotom_net_edge(uint64_t role) {
    if (leanos_blocking_ipc_event(qotom_net_ipc_step, qotom_net_ipc_step + 1, role) !=
            qotom_net_ipc_words[qotom_net_ipc_step])
        qotom_blocking_fail("qotom-net-ipc-model");
    qotom_net_ipc_step = (qotom_net_ipc_step + 1) & 3u;
    qotom_net_ipc_edges++;
}

/* A frame into A's buffer at `address`, through the writable copy-out root. */
static void qotom_net_copy_out(uint64_t address, const uint8_t *source, uint64_t length) {
    for (uint64_t done = 0; done < length;) {
        uint64_t n = length - done < 16 ? length - done : 16;
        for (uint64_t i = 0; i < n; ++i)
            qotom_net_operands[i] = (struct qotom_copy_operand){
                (uint64_t)&source[done + i],
                qotom_alias_address(address + done + i, qotom_copy_out_aliases)};
        if (leanos_copy_root_transfer(qotom_entry_closed_root,
                (uint64_t)qotom_copy_out_root.pml4, qotom_net_operands, n) != n)
            qotom_blocking_fail("qotom-net-copy-out");
        done += n;
    }
}

/* A reply out of A's buffer at `address`, through the read-only copy root. */
static void qotom_net_copy_in(uint8_t *destination, uint64_t address, uint64_t length) {
    for (uint64_t done = 0; done < length;) {
        uint64_t n = length - done < 16 ? length - done : 16;
        for (uint64_t i = 0; i < n; ++i)
            qotom_net_operands[i] = (struct qotom_copy_operand){
                qotom_alias_address(address + done + i, qotom_aliases),
                (uint64_t)&destination[done + i]};
        if (leanos_copy_root_transfer(qotom_entry_closed_root,
                (uint64_t)qotom_copy_root.pml4, qotom_net_operands, n) != n)
            qotom_blocking_fail("qotom-net-copy-in");
        done += n;
    }
}

static uint64_t qotom_net_refuse(const char *operation, uint64_t reason) {
    qotom_net_refusals++;
    serial_puts("LEANOS-LAB/1 NET event=refuse subject=");
    serial_u64(current_subject);
    serial_puts(" op="); serial_puts(operation);
    serial_puts(" reason="); serial_u64(reason);
    serial_puts(" model=refused\n");
    return QOTOM_NET_REFUSED | reason;
}

/* Frame copies (64 fetch, 65 send), decided by the generated witness. */
static uint64_t qotom_net_copy(uint64_t *saved, uint64_t number) {
    const uint64_t base = (uint64_t)user_a_stack;
    const uint64_t limit = base + QOTOM_NET_STACK_BYTES;
    uint64_t address = saved[13], length = saved[12];
    uint64_t fetch = number == 64;
    uint64_t pending = fetch ? qotom_net_rx_pending : qotom_net_tx_pending;
    if (fetch) length = qotom_net_rx_len;
#ifdef LEANOS_QOTOM_DHCP_SUBJECT
    /* The caller's own window, labelled with the caller; the endpoint
       serves A's current occupant. */
    uint64_t model = qotom_net_model_subject();
    uint64_t witness = leanos_frame_port_check(model,
        (fetch ? 1u : 2u) | pending << 8 | (qotom_net_a_model & 0xffu) << 16 |
            (model & 0xffu) << 24, address, length, base, limit);
#else
    uint64_t witness = leanos_frame_copy_check(qotom_net_model_subject(),
        (fetch ? 1u : 2u) | pending << 8, address, length, base, limit);
#endif
    if (witness != 0) return qotom_net_refuse(fetch ? "fetch" : "send", witness);
    if (current_subject != 1 || qotom_blocking_step != 32)
        qotom_blocking_fail("qotom-net-copy-sequence");
    if (fetch) {
        qotom_net_copy_out(address, qotom_net_scratch() + QOTOM_NET_RX_AT, length);
        qotom_net_rx_pending = 0;
        qotom_net_fetches++;
    } else {
        qotom_net_copy_in(qotom_net_scratch() + QOTOM_NET_TX_AT, address, length);
        *(volatile uint32_t *)(qotom_net_scratch() + QOTOM_NET_TX_LEN_AT) = (uint32_t)length;
        qotom_net_tx_pending = 1;
        qotom_net_tx_len = length;
        qotom_net_replies++;
    }
    serial_puts(fetch ? "LEANOS-LAB/1 NET event=fetch frame=" : "LEANOS-LAB/1 NET event=send frame=");
    serial_u64(qotom_net_seq);
    serial_puts(" bytes="); serial_u64(length);
    serial_puts(" copy-roots=bounded16 model=accepted\n");
    return fetch ? length : 0;
}

/* B's next frame: hand the pending reply to the program, resume it until it
   yields the next frame (or halts). */
static uint64_t qotom_net_next_frame(void) {
    if (qotom_net_ended) return 0;
    if (qotom_net_rx_pending) qotom_blocking_fail("qotom-net-frame-unfetched");
    volatile uint32_t *tx_len = (volatile uint32_t *)(qotom_net_scratch() + QOTOM_NET_TX_LEN_AT);
    if (*tx_len != (qotom_net_tx_pending ? qotom_net_tx_len : 0))
        qotom_blocking_fail("qotom-net-transmit-slot");
    qotom_net_tx_pending = 0;
#ifdef LEANOS_QOTOM_LONG_SESSION
    if (qotom_watchdog_session_spent()) {
        /* A reply still in the slot is not sent: the program is not
           resumed again.  FINAL reports it. */
        qotom_wd_unsent = *tx_len != 0;
        *tx_len = 0;
        qotom_wd_budget_end = 1;
        qotom_net_ended = 1;
        return 0;
    }
#endif
    uint64_t code = lab_stream_next_key();
    if (*tx_len != 0) qotom_blocking_fail("qotom-net-transmit-not-taken");
    if (code == 0) {
        qotom_net_ended = 1;
        return 0;
    }
#ifdef LEANOS_QOTOM_DHCP_SUBJECT
    if (qotom_net_seq == 0 ? code != QOTOM_NET_LINK_BYTES
        : code != QOTOM_NET_TICK_BYTES &&
          (code < QOTOM_NET_FRAME_MIN || code > QOTOM_NET_FRAME_MAX))
        qotom_blocking_fail("qotom-net-frame-length");
#else
    if (qotom_net_seq == 0 ? code != QOTOM_NET_CONFIG_BYTES
        : code < QOTOM_NET_FRAME_MIN || code > QOTOM_NET_FRAME_MAX)
        qotom_blocking_fail("qotom-net-frame-length");
#endif
#ifdef LEANOS_QOTOM_LONG_SESSION
    if (qotom_net_seq == 0) qotom_watchdog_progress(QOTOM_WATCHDOG_LINK);
    else if (code == QOTOM_NET_TICK_BYTES) qotom_watchdog_progress(QOTOM_WATCHDOG_TICK);
#endif
    qotom_net_rx_len = code;
    qotom_net_rx_pending = 1;
    ++qotom_net_seq;
    serial_puts("LEANOS-LAB/1 NET event=deliver frame=");
    serial_u64(qotom_net_seq);
    serial_puts(" bytes="); serial_u64(code);
    serial_putc('\n');
    return qotom_net_seq << 32 | code;
}

#ifdef LEANOS_QOTOM_DHCP_SUBJECT
/* The hand-off (issue #556): the DHCP subject, serving a record, sends its
   lease (hardware address in RBX, IPv4 address in RCX) on endpoint 13.  The
   kernel holds it, zeroes both of A's stack pages through the writable
   copy-out root, and restarts A fresh at the echo subject's entry. */
static uint64_t qotom_net_handoff(uint64_t *saved) {
    if (qotom_net_a_model != QOTOM_NET_MODEL_DHCP || qotom_blocking_step != 32 ||
        qotom_net_rx_pending || qotom_net_tx_pending ||
        saved[13] >> 48 != 0 || saved[12] >> 32 != 0)
        qotom_blocking_fail("qotom-net-handoff");
    qotom_net_lease_mac = saved[13];
    qotom_net_lease_ip = saved[12];
    qotom_net_lease_held = 1;
    qotom_net_handoff_seq = qotom_net_seq;
    for (uint64_t done = 0; done < QOTOM_NET_STACK_BYTES; done += 16)
        qotom_net_copy_out((uint64_t)user_a_stack + done, qotom_net_zeros, 16);
    qotom_net_a_model = QOTOM_NET_MODEL_NETWORK;
    qotom_initial_a_frame(saved);
    saved[15] = (uint64_t)qotom_echo_subject_entry;
    serial_puts("LEANOS-LAB/1 NET event=handoff from=dhcp-subject to=echo-subject frame=");
    serial_u64(qotom_net_seq);
    serial_puts(" lease=");
    serial_u64(qotom_net_lease_ip >> 24 & 0xffu); serial_putc('.');
    serial_u64(qotom_net_lease_ip >> 16 & 0xffu); serial_putc('.');
    serial_u64(qotom_net_lease_ip >> 8 & 0xffu); serial_putc('.');
    serial_u64(qotom_net_lease_ip & 0xffu);
    serial_puts(" scrubbed=8192 restart=echo-entry model=accepted\n");
    return qotom_entry_subject_root;
}
#endif

/* The network-subject continuation after the fixed first exchange.  Steps:
   30 A runs (its send returned), 31 B drives, 32 A serves a frame. */
static uint64_t qotom_net_dispatch(uint64_t *saved, uint64_t number) {
    if (current_subject == 1 && qotom_net_ipc_step == 3)
        qotom_net_edge(2);
    if (number == 60) {
        uint64_t model = qotom_net_model_subject();
        uint64_t holder = model == QOTOM_NET_MODEL_DRIVER;
        if (leanos_device_authorize(model, 0) != (holder ? 1u : 2u))
            qotom_blocking_fail("qotom-net-device-model");
        if (!holder) {
            qotom_net_refusals++;
            serial_puts("LEANOS-LAB/1 NET event=refuse subject=1 op=device-invoke reason=no-device-capability model=refused\n");
            saved[14] = QOTOM_NET_REFUSED | 7u;
            return (uint64_t)page_map_level_4_a;
        }
        if (qotom_blocking_step != 31 || !qotom_net_waiting)
            qotom_blocking_fail("qotom-net-device-sequence");
        saved[14] = qotom_net_next_frame();
        return (uint64_t)page_map_level_4_b;
    }
    if (number == 64 || number == 65) {
        saved[14] = qotom_net_copy(saved, number);
        return qotom_entry_subject_root;
    }
#ifdef LEANOS_QOTOM_DHCP_SUBJECT
    if (number == 8 && current_subject == 1 && saved[11] == QOTOM_NET_LEASE_ENDPOINT)
        return qotom_net_handoff(saved);
    if (number == 7 && current_subject == 1 && saved[11] == QOTOM_NET_LEASE_ENDPOINT) {
        /* The echo subject takes the held lease. */
        if (qotom_net_a_model != QOTOM_NET_MODEL_NETWORK || !qotom_net_lease_held)
            qotom_blocking_fail("qotom-net-lease-receive");
        qotom_net_lease_held = 0;
        saved[14] = qotom_net_lease_mac;
        saved[13] = qotom_net_lease_ip;
        saved[12] = 1;
        serial_puts(LEANOS_SERIAL_10_IPC " event=deliver receiver=1 endpoint=13 role=echo-subject payload=lease\n");
        return qotom_entry_subject_root;
    }
#endif
    if (number == 7 && current_subject == 1 &&
        (qotom_blocking_step == 30 || qotom_blocking_step == 32)) {
        if (qotom_net_waiting || qotom_net_rx_pending)
            qotom_blocking_fail("qotom-net-receive-sequence");
        qotom_net_waiting = 1;
        qotom_net_edge(2);
        qotom_copy_frame(qotom_saved_a, saved);
        qotom_copy_frame(saved, qotom_saved_b);
        saved[14] = 0;
        qotom_blocking_step = 31;
        current_subject = 2;
        qotom_entry_subject_root = (uint64_t)page_map_level_4_b;
        serial_puts(LEANOS_SERIAL_10_IPC " event=block subject=1 endpoint=10 role=network-subject\n");
        return qotom_entry_subject_root;
    }
    if (number == 8 && current_subject == 2 && qotom_blocking_step == 31) {
        if (!qotom_net_waiting || !qotom_net_rx_pending ||
            saved[13] != qotom_net_rx_len || saved[12] != qotom_net_seq)
            qotom_blocking_fail("qotom-net-send");
        qotom_net_edge(1);
        qotom_net_edge(1);
        qotom_net_waiting = 0;
        qotom_copy_frame(qotom_saved_b, saved);
        qotom_copy_frame(saved, qotom_saved_a);
        saved[14] = qotom_net_rx_len;
        saved[13] = qotom_net_seq;
        saved[12] = 1;
        qotom_blocking_step = 32;
        current_subject = 1;
        qotom_entry_subject_root = (uint64_t)page_map_level_4_a;
        serial_puts(LEANOS_SERIAL_10_IPC " event=send sender=2 endpoint=10 payload0=");
        serial_u64(qotom_net_rx_len);
        serial_puts(" payload1="); serial_u64(qotom_net_seq);
        serial_puts(" receiver=1 accepted=1\n");
        return qotom_entry_subject_root;
    }
    if (number == 61 && current_subject == 2 && qotom_blocking_step == 31) {
        if (!qotom_net_ended || qotom_net_fetches != qotom_net_seq ||
            qotom_net_rx_pending || qotom_net_tx_pending || !qotom_net_waiting ||
            qotom_net_ipc_step != 1)
            qotom_blocking_fail("qotom-net-count");
#ifdef LEANOS_QOTOM_DHCP_SUBJECT
        if (qotom_net_a_model != QOTOM_NET_MODEL_NETWORK || qotom_net_lease_held ||
            qotom_net_handoff_seq == 0)
            qotom_blocking_fail("qotom-net-lease-count");
        serial_puts(LEANOS_SERIAL_10_FINAL " status=PASS dhcp-subject=1 echo-subject=1 device-holder=2 dhcp-frames=");
        serial_u64(qotom_net_handoff_seq);
        serial_puts(" lease=");
        serial_u64(qotom_net_lease_ip >> 24 & 0xffu); serial_putc('.');
        serial_u64(qotom_net_lease_ip >> 16 & 0xffu); serial_putc('.');
        serial_u64(qotom_net_lease_ip >> 8 & 0xffu); serial_putc('.');
        serial_u64(qotom_net_lease_ip & 0xffu);
        serial_puts(" frames=");
#else
        serial_puts(LEANOS_SERIAL_10_FINAL " status=PASS network-subject=1 device-holder=2 frames=");
#endif
        serial_u64(qotom_net_seq);
        serial_puts(" fetches="); serial_u64(qotom_net_fetches);
        serial_puts(" replies="); serial_u64(qotom_net_replies);
        serial_puts(" refusals="); serial_u64(qotom_net_refusals);
        serial_puts(" ipc-edges="); serial_u64(qotom_net_ipc_edges);
#ifdef LEANOS_QOTOM_LONG_SESSION
        serial_puts(" watchdog-kicks="); serial_u64(qotom_wd_kicks);
        serial_puts(qotom_wd_budget_end ? " session-end=budget unsent-replies="
                                         : " session-end=window unsent-replies=");
        serial_u64(qotom_wd_unsent);
#endif
        serial_putc('\n');
        for (;;) __asm__ volatile("cli; hlt");
    }
    qotom_blocking_fail("qotom-net-sequence");
}
