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
 * scratch is LeanOS.Net.FrameSource's. */
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
/* The executor scratch (hardware/wifi/wifi-exec.h, spliced after this file). */
static uint8_t *qotom_net_scratch(void);

static uint64_t qotom_net_model_subject(void) {
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
    uint64_t witness = leanos_frame_copy_check(qotom_net_model_subject(),
        (fetch ? 1u : 2u) | pending << 8, address, length, base, limit);
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
    uint64_t code = lab_stream_next_key();
    if (*tx_len != 0) qotom_blocking_fail("qotom-net-transmit-not-taken");
    if (code == 0) {
        qotom_net_ended = 1;
        return 0;
    }
    if (qotom_net_seq == 0 ? code != QOTOM_NET_CONFIG_BYTES
        : code < QOTOM_NET_FRAME_MIN || code > QOTOM_NET_FRAME_MAX)
        qotom_blocking_fail("qotom-net-frame-length");
    qotom_net_rx_len = code;
    qotom_net_rx_pending = 1;
    ++qotom_net_seq;
    serial_puts("LEANOS-LAB/1 NET event=deliver frame=");
    serial_u64(qotom_net_seq);
    serial_puts(" bytes="); serial_u64(code);
    serial_putc('\n');
    return qotom_net_seq << 32 | code;
}

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
        serial_puts(LEANOS_SERIAL_10_FINAL " status=PASS network-subject=1 device-holder=2 frames=");
        serial_u64(qotom_net_seq);
        serial_puts(" fetches="); serial_u64(qotom_net_fetches);
        serial_puts(" replies="); serial_u64(qotom_net_replies);
        serial_puts(" refusals="); serial_u64(qotom_net_refusals);
        serial_puts(" ipc-edges="); serial_u64(qotom_net_ipc_edges);
        serial_putc('\n');
        for (;;) __asm__ volatile("cli; hlt");
    }
    qotom_blocking_fail("qotom-net-sequence");
}
