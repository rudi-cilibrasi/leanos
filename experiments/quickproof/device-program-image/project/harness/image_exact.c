/* Law image_exact.  For every image (any 32-bit length, an object of exactly that many bytes holding any bytes),
   every prior value of every object a function may write (the target, the policy, the header length, the executor
   state and the 262144-byte executor scratch), and every pair of targets and of policies with at most 8 address
   sinks and 16 descriptors each but any other field values, main calls one entry point of
   hardware/wifi/wifi-exec.h (patch/device_program_unit.c), and it behaves as follows.  Words are little-endian
   32-bit values of the image: word@k is bytes k..k+3.  BAD is WIFI_BAD_IMAGE.
     - Header (wifi_image_header): it returns 0 exactly when the image has at least 16 bytes, word@0 is the magic
       0x4649574c ("LWIF") and either
         * word@4 (the version) is 1: then the target is the BCM43224 (bus 2, device 0, function 0, identity
           0x435314e4, window 0x4000, BAR offset 0x10), the policy is absent and the header length is 16; or
         * the version is 2 or 3 and the image has at least 32 bytes (version 2) or 68 bytes (version 3); word@16
           (BDF) has no bit set outside bits 16..23 (bus), 8..12 (device) and 0..2 (function); the BAR offset,
           word@28 or 0x10 when word@28 is 0, is a multiple of 4 from 0x10 to 0x24; and the window word@24 is a
           nonzero multiple of 512 of at most 0x10000.  Then the target is that bus, device and function, identity
           word@20, that window and that BAR offset.  Version 2 has no policy and the header length is 32.
           Version 3 also requires: the flags word@32 at most 3, the target's window at most the policy window
           word@36, the sink count S = word@64 at most 8, and at least 68 + 4S bytes.  Its policy is present, with
           DMA flags bit 0, window word@36, configuration read and write bitmaps word@40 | word@44 << 32 and
           word@48 | word@52 << 32, command clear and set masks word@56 and word@60, and the S address sinks
           word@68, word@72, ...; the header length is 68 + 4S.  When flags bit 1 is set, the descriptor map
           follows at A = 68 + 4S: it requires at least A + 4 bytes, a count D = word@A of at most 16 and at least
           A + 4 + 16D bytes, and each descriptor i, the words (kind, start, count, stride) at A + 4 + 16i, to have
           kind 0 or 1, a count from 1 to 4096 and its limit start + stride * (count - 1) + (16 for kind 1, 8 for
           kind 0), computed without overflow, at most 262144 (the scratch).  The policy then has those D
           descriptors and the header length is A + 4 + 16D.  Without flags bit 1 it has none.
       Otherwise it returns BAD.  On 0 it writes exactly that target, header length and policy (an absent policy
       has every scalar field 0, including present, the sink count and the descriptor count); the policy's sink
       and descriptor entries past its counts keep their values.  On BAD the target, policy and header length are
       unspecified.
     - Start (wifi_start): it returns 0 exactly when the header returns 0 and, with N = word@8 and B = word@12 and
       H the header length, N is at most (length - H) / 16 and B is length - H - 16N.  Then the executor state has
       the header's target and policy (as above), the target's window, N, B, the code at image + H and the blob at
       image + H + 16N, all sixteen registers 0, stack pointer, program counter and step count 0, and its stack
       entries unchanged; every scratch byte is 0.  Otherwise it returns BAD, the scratch and every field of the
       executor state but its target and policy keep their values.
     - Within (wifi_policy_within, policies p and max): it returns 1 exactly when p declares every address sink of
       max and every descriptor of max (all four fields equal), p's window and DMA field are at most max's, and
       p's configuration bitmaps and command masks have no bit outside max's; else 0.
     - Service (wifi_service_admitted, target t, policy p, target want, policy max): it returns 1 exactly when t
       equals want in all six fields, p's present field is nonzero and Within(p, max) is 1; else 0.
     - Source (wifi_source_admitted, target t, policy p, policy max): it returns 1 exactly when t is bus 0, device
       0, function 0, identity 0xffffffff with max's window, p's present field is nonzero, p declares no sink and
       no descriptor, p's window is at most max's, and p's DMA field, both bitmaps and both masks are 0; else 0.
     - No function writes the image.
   So no image makes the parser return a target, window, BAR offset, policy, sink or descriptor that the image
   does not encode, accept a region outside the scratch or a field the format rejects, or start a program whose
   code and blob are not exactly the bytes after the header; and the admission returns exactly the subset test
   above.  The format is the one LeanOS.Wifi.Bytecode.Program.image writes; the header also accepts an explicit
   BAR offset 0x10 and an empty descriptor map under flags bit 1, which that encoder never writes, with the same
   meaning.  Not claimed: termination (partial correctness; every loop is bounded); what a policy permits
   (LeanOS.DeviceProgramConfinement); that a kernel's profile is the Lean policy it mirrors; a NULL or
   overlapping argument (the kernel passes its program array and static objects). */
#include <stdlib.h>
#include "quickproof.h"
#include "image_exact.h"

struct law law;

/* word@at of the law's copy. */
static uint32_t word_at(const uint8_t *b, uint32_t at) {
    return (uint32_t)b[at] | (uint32_t)b[at + 1] << 8 | (uint32_t)b[at + 2] << 16 | (uint32_t)b[at + 3] << 24;
}

/* The law's reading of the image: the status and fields the law comment states. */
static void read_image(const uint8_t *b, uint32_t len, struct law_image *r) {
    struct wifi_policy *p = &r->pol;
    r->status = WIFI_BAD_IMAGE;
    r->start_status = WIFI_BAD_IMAGE;
    if (len < 16 || word_at(b, 0) != 0x4649574cu)
        return;
    uint32_t version = word_at(b, 4);
    p->present = 0;
    p->dma = 0;
    p->window = 0;
    p->cfg_read = 0;
    p->cfg_write = 0;
    p->cmd_clear = 0;
    p->cmd_set = 0;
    p->sink_count = 0;
    p->desc_count = 0;
    uint32_t at = 16;
    if (version == 1) {
        r->t.bus = 2;
        r->t.dev = 0;
        r->t.fn = 0;
        r->t.id = 0x435314e4u;
        r->t.window = 0x4000u;
        r->t.bar = 0x10u;
    } else {
        if (version != 2 && version != 3)
            return;
        if (len < (version == 2 ? 32u : 68u))
            return;
        uint32_t bdf = word_at(b, 16);
        uint32_t window = word_at(b, 24);
        uint32_t bar = word_at(b, 28);
        if (bar == 0)
            bar = 0x10u;
        if ((bdf >> 24) != 0 || ((bdf >> 13) & 7u) != 0 || ((bdf >> 3) & 31u) != 0)
            return;
        if (bar < 0x10u || bar > 0x24u || bar % 4u != 0)
            return;
        if (window == 0 || window > 0x10000u || window % 512u != 0)
            return;
        r->t.bus = bdf >> 16;
        r->t.dev = (bdf >> 8) & 31u;
        r->t.fn = bdf & 7u;
        r->t.id = word_at(b, 20);
        r->t.window = window;
        r->t.bar = bar;
        at = 32;
        if (version == 3) {
            uint32_t flags = word_at(b, 32);
            uint32_t sinks = word_at(b, 64);
            if (flags > 3u || window > word_at(b, 36) || sinks > 8u || len < 68u + 4u * sinks)
                return;
            p->present = 1;
            p->dma = flags & 1u;
            p->window = word_at(b, 36);
            p->cfg_read = (uint64_t)word_at(b, 44) << 32 | word_at(b, 40);
            p->cfg_write = (uint64_t)word_at(b, 52) << 32 | word_at(b, 48);
            p->cmd_clear = word_at(b, 56);
            p->cmd_set = word_at(b, 60);
            p->sink_count = sinks;
            for (uint32_t i = 0; i < sinks; ++i)
                p->sinks[i] = word_at(b, 68 + 4 * i);
            at = 68 + 4 * sinks;
            if (flags & 2u) {
                if (len < at + 4u)
                    return;
                uint32_t descs = word_at(b, at);
                if (descs > 16u || len < at + 4u + 16u * descs)
                    return;
                for (uint32_t i = 0; i < descs; ++i) {
                    uint32_t e = at + 4 + 16 * i;
                    uint32_t kind = word_at(b, e), start = word_at(b, e + 4);
                    uint32_t count = word_at(b, e + 8), stride = word_at(b, e + 12);
                    if (kind > 1u || count == 0 || count > 4096u)
                        return;
                    if ((uint64_t)start + (uint64_t)stride * (count - 1u) + (kind ? 16u : 8u) > 262144u)
                        return;
                    p->descs[i].trb = kind;
                    p->descs[i].start = start;
                    p->descs[i].count = count;
                    p->descs[i].stride = stride;
                }
                p->desc_count = descs;
                at = at + 4 + 16 * descs;
            }
        }
    }
    r->status = 0;
    r->header_len = at;
    r->n = word_at(b, 8);
    r->blob_len = word_at(b, 12);
    if (r->n <= (len - at) / 16 && r->blob_len == len - at - 16 * r->n)
        r->start_status = 0;
}

static void any_target(struct wifi_target *t) {
    t->bus = nondet_u32();
    t->dev = nondet_u32();
    t->fn = nondet_u32();
    t->id = nondet_u32();
    t->window = nondet_u32();
    t->bar = nondet_u32();
}

static uint64_t any_u64(void) {
    uint64_t hi = nondet_u32();
    uint64_t lo = nondet_u32();
    return hi << 32 | lo;
}

/* Any policy; with `bounded`, at most 8 sinks and 16 descriptors. */
static void any_policy(struct wifi_policy *p, int bounded) {
    p->present = nondet_u32();
    p->dma = nondet_u32();
    p->window = nondet_u32();
    p->cfg_read = any_u64();
    p->cfg_write = any_u64();
    p->cmd_clear = nondet_u32();
    p->cmd_set = nondet_u32();
    p->sink_count = nondet_u32();
    for (uint32_t i = 0; i < WIFI_MAX_SINKS; ++i)
        p->sinks[i] = nondet_u32();
    p->desc_count = nondet_u32();
    for (uint32_t i = 0; i < WIFI_MAX_DESCS; ++i) {
        p->descs[i].trb = nondet_u32();
        p->descs[i].start = nondet_u32();
        p->descs[i].count = nondet_u32();
        p->descs[i].stride = nondet_u32();
    }
    if (bounded) {
        p->sink_count %= WIFI_MAX_SINKS + 1;
        p->desc_count %= WIFI_MAX_DESCS + 1;
    }
}

static void copy_policy(struct wifi_policy *d, const struct wifi_policy *s) {
    d->present = s->present;
    d->dma = s->dma;
    d->window = s->window;
    d->cfg_read = s->cfg_read;
    d->cfg_write = s->cfg_write;
    d->cmd_clear = s->cmd_clear;
    d->cmd_set = s->cmd_set;
    d->sink_count = s->sink_count;
    for (uint32_t i = 0; i < WIFI_MAX_SINKS; ++i)
        d->sinks[i] = s->sinks[i];
    d->desc_count = s->desc_count;
    for (uint32_t i = 0; i < WIFI_MAX_DESCS; ++i) {
        d->descs[i].trb = s->descs[i].trb;
        d->descs[i].start = s->descs[i].start;
        d->descs[i].count = s->descs[i].count;
        d->descs[i].stride = s->descs[i].stride;
    }
}

static int same_target(const struct wifi_target *a, const struct wifi_target *b) {
    return a->bus == b->bus && a->dev == b->dev && a->fn == b->fn && a->id == b->id && a->window == b->window &&
           a->bar == b->bar;
}

static int same_desc(const struct wifi_desc *a, const struct wifi_desc *b) {
    return a->trb == b->trb && a->start == b->start && a->count == b->count && a->stride == b->stride;
}

/* A parsed policy: the law's reading in every scalar field and in the entries below its counts, the prior values
   in the entries past them. */
static void check_policy(const struct wifi_policy *got, const struct wifi_policy *want,
                         const struct wifi_policy *prior) {
    qp_assert(got->present == want->present && got->dma == want->dma && got->window == want->window);
    qp_assert(got->cfg_read == want->cfg_read && got->cfg_write == want->cfg_write);
    qp_assert(got->cmd_clear == want->cmd_clear && got->cmd_set == want->cmd_set);
    qp_assert(got->sink_count == want->sink_count && got->desc_count == want->desc_count);
    for (uint32_t i = 0; i < WIFI_MAX_SINKS; ++i) {
        if (i < want->sink_count)
            qp_assert(got->sinks[i] == want->sinks[i]);
        else
            qp_assert(got->sinks[i] == prior->sinks[i]);
    }
    for (uint32_t i = 0; i < WIFI_MAX_DESCS; ++i) {
        if (i < want->desc_count)
            qp_assert(same_desc(&got->descs[i], &want->descs[i]) != 0);
        else
            qp_assert(same_desc(&got->descs[i], &prior->descs[i]) != 0);
    }
}

static void header_case(struct law *m, const uint8_t *image) {
    struct wifi_target t;
    struct wifi_policy pol, prior;
    any_target(&t);
    any_policy(&pol, 0);
    copy_policy(&prior, &pol);
    uint32_t header_len = nondet_u32();
    int status = dp_header(image, m->length, &t, &pol, &header_len);
    qp_assert(status == (int)m->want.status);
    if (status == 0) {
        qp_assert(same_target(&t, &m->want.t) != 0);
        qp_assert(header_len == m->want.header_len);
        check_policy(&pol, &m->want.pol, &prior);
    }
}

static void start_case(struct law *m, const uint8_t *image) {
    struct wifi_vm *vm = malloc(sizeof(struct wifi_vm));
    struct wifi_vm *prior = malloc(sizeof(struct wifi_vm));
    uint8_t *saved = malloc(WIFI_SCRATCH_BYTES);
    if (vm == NULL || prior == NULL || saved == NULL)
        return;
    vm->code_base = NULL;
    vm->blob = NULL;
    vm->n = nondet_u32();
    vm->blob_len = nondet_u32();
    vm->window = nondet_u32();
    any_policy(&vm->pol, 0);
    any_target(&vm->target);
    for (uint32_t i = 0; i < 16; ++i)
        vm->r[i] = nondet_u32();
    for (uint32_t i = 0; i < WIFI_STACK_DEPTH; ++i)
        vm->stack[i] = nondet_u32();
    vm->sp = nondet_u32();
    vm->pc = nondet_u32();
    vm->steps = any_u64();
    prior->n = vm->n;
    prior->blob_len = vm->blob_len;
    prior->window = vm->window;
    copy_policy(&prior->pol, &vm->pol);
    for (uint32_t i = 0; i < 16; ++i)
        prior->r[i] = vm->r[i];
    for (uint32_t i = 0; i < WIFI_STACK_DEPTH; ++i)
        prior->stack[i] = vm->stack[i];
    prior->sp = vm->sp;
    prior->pc = vm->pc;
    prior->steps = vm->steps;
    uint8_t *scratch = dp_scratch();
    nondet_bytes(scratch, WIFI_SCRATCH_BYTES);
    for (uint32_t i = 0; i < WIFI_SCRATCH_BYTES; ++i)
        saved[i] = scratch[i];

    int status = dp_start(vm, image, m->length);
    if (m->want.status != 0 || m->want.start_status != 0) {
        qp_assert(status == WIFI_BAD_IMAGE);
        qp_assert(vm->code_base == NULL && vm->blob == NULL);
        qp_assert(vm->n == prior->n && vm->blob_len == prior->blob_len && vm->window == prior->window);
        for (uint32_t i = 0; i < 16; ++i)
            qp_assert(vm->r[i] == prior->r[i]);
        qp_assert(vm->sp == prior->sp && vm->pc == prior->pc && vm->steps == prior->steps);
        for (uint32_t i = 0; i < WIFI_SCRATCH_BYTES; ++i)
            qp_assert(scratch[i] == saved[i]);
    } else {
        qp_assert(status == 0);
        qp_assert(same_target(&vm->target, &m->want.t) != 0);
        check_policy(&vm->pol, &m->want.pol, &prior->pol);
        qp_assert(vm->window == m->want.t.window && vm->n == m->want.n && vm->blob_len == m->want.blob_len);
        qp_assert(vm->code_base == image + m->want.header_len);
        qp_assert(vm->blob == image + m->want.header_len + 16u * m->want.n);
        for (uint32_t i = 0; i < 16; ++i)
            qp_assert(vm->r[i] == 0);
        qp_assert(vm->sp == 0 && vm->pc == 0 && vm->steps == 0);
        for (uint32_t i = 0; i < WIFI_SCRATCH_BYTES; ++i)
            qp_assert(scratch[i] == 0);
    }
    for (uint32_t i = 0; i < WIFI_STACK_DEPTH; ++i)
        qp_assert(vm->stack[i] == prior->stack[i]);
}

static int declares_sink(const struct wifi_policy *p, uint32_t off) {
    int found = 0;
    for (uint32_t i = 0; i < p->sink_count; ++i)
        if (p->sinks[i] == off)
            found = 1;
    return found;
}

static int declares_desc(const struct wifi_policy *p, const struct wifi_desc *d) {
    int found = 0;
    for (uint32_t i = 0; i < p->desc_count; ++i)
        if (same_desc(&p->descs[i], d))
            found = 1;
    return found;
}

/* Within(p, max) of the law comment. */
static int within(const struct wifi_policy *p, const struct wifi_policy *max) {
    int ok = p->window <= max->window && p->dma <= max->dma && (p->cfg_read & ~max->cfg_read) == 0 &&
             (p->cfg_write & ~max->cfg_write) == 0 && (p->cmd_clear & ~max->cmd_clear) == 0 &&
             (p->cmd_set & ~max->cmd_set) == 0;
    for (uint32_t k = 0; k < max->sink_count; ++k)
        if (!declares_sink(p, max->sinks[k]))
            ok = 0;
    for (uint32_t k = 0; k < max->desc_count; ++k)
        if (!declares_desc(p, &max->descs[k]))
            ok = 0;
    return ok;
}

static void admission_case(struct law *m) {
    struct wifi_target t, want;
    struct wifi_policy p, max;
    any_target(&t);
    any_target(&want);
    any_policy(&p, 1);
    any_policy(&max, 1);
    int expect, got;
    if (m->call == CALL_WITHIN) {
        expect = within(&p, &max);
        got = dp_within(&p, &max);
    } else if (m->call == CALL_SERVICE) {
        expect = same_target(&t, &want) && p.present != 0 && within(&p, &max);
        got = dp_service(&t, &p, &want, &max);
    } else {
        expect = t.bus == 0 && t.dev == 0 && t.fn == 0 && t.id == 0xffffffffu && t.window == max.window &&
                 p.present != 0 && p.sink_count == 0 && p.desc_count == 0 && p.window <= max.window && p.dma == 0 &&
                 p.cfg_read == 0 && p.cfg_write == 0 && p.cmd_clear == 0 && p.cmd_set == 0;
        got = dp_source(&t, &p, &max);
    }
    qp_assert(got == expect);
}

int main(void) {
    struct law *m = &law;
    uint8_t call = nondet_u8();
    m->call = call < CALL_SOURCE ? call : CALL_SOURCE;
    m->length = 0;
    m->copy = NULL;
    m->want.status = WIFI_BAD_IMAGE;
    m->want.start_status = WIFI_BAD_IMAGE;
    if (m->call > CALL_START) {
        admission_case(m);
        return 0;
    }
    m->length = nondet_u32();
    uint8_t *image = malloc(m->length);
    m->copy = malloc(m->length);
    if (image == NULL || m->copy == NULL)
        return 0;
    nondet_bytes(image, m->length);
    for (uint32_t i = 0; i < m->length; ++i)
        m->copy[i] = image[i];
    read_image(m->copy, m->length, &m->want);
    if (m->call == CALL_HEADER)
        header_case(m, image);
    else
        start_case(m, image);
    for (uint32_t i = 0; i < m->length; ++i)
        qp_assert(image[i] == m->copy[i]);
    return 0;
}
