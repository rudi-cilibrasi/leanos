/* The device-program executor (issue #494, ADR 0020).

   The instruction step is not written here: it is
   `leanos_device_program_step`, the C the Lean compiler generates for
   `LeanOS.Wifi.Exec.step` (LeanOS/Wifi/Exec.lean), which
   `LeanOS.Wifi.ExecRefinement.step_eq` proves equal to `Sim.step`. It is the
   only interpreter: the booted device-service kernel, the lab kernel and the
   hosted runners all execute programs through it. This file supplies only

   * the named hook primitives `wifi_gen_*` that step calls, each a direct
     reading or update of the executor state of `wifi-exec.h` (registers, pc,
     return stack, scratch) or one device effect through the WH_* hooks; their
     Lean meaning is `LeanOS.Wifi.ExecRefinement.instHooksSt`; and
   * `wifi_gen_resume`, the step loop (`Sim.loop`/`Sim.resume`), and
     `wifi_exec`, start-and-run.

   Image parsing and `wifi_start` are those of `wifi-exec.h`. Include this
   file in exactly one translation unit and link the generated C of
   LeanOS/Wifi/Exec.lean: the hooks have external linkage because the
   generated step calls them by name. The generated step ignores the token a
   hook receives except to pass it on; a hook's result is the value it
   delivers (or anything, for updates), which keeps the generated calls in
   program order. */
#ifndef LEANOS_WIFI_GEN_EXEC_H
#define LEANOS_WIFI_GEN_EXEC_H

#include "wifi-exec.h"

#define WIFI_GEN_NEXT 12u

/* The generated step (LeanOS.Wifi.Exec.deviceProgramStep). */
uint64_t leanos_device_program_step(uint64_t);

/* The executor the hooks act on: set by wifi_gen_resume for one call. */
static struct wifi_vm *wifi_gen_vm;
static const struct wifi_hooks *wifi_gen_h;
static uint32_t wifi_gen_status, wifi_gen_code;

#define WG_HOOKS const struct wifi_hooks *const h = wifi_gen_h; (void)h

/* withVal: a computed value handed on as the token. */
uint64_t wifi_gen_value(uint64_t t, uint64_t x) { (void)t; return x; }

/* Image constants and the declared policy (immutable during a run). */
uint32_t wifi_gen_window(uint64_t t) { (void)t; return wifi_gen_vm->window; }
uint32_t wifi_gen_blob_len(uint64_t t) { (void)t; return wifi_gen_vm->blob_len; }
uint32_t wifi_gen_blob_word(uint64_t t, uint32_t off) {
    (void)t;
    uint32_t v = 0;
    for (uint32_t i = 0; i < 4; ++i)
        if ((uint64_t)off + i < wifi_gen_vm->blob_len)
            v |= (uint32_t)wifi_gen_vm->blob[(uint64_t)off + i] << (8 * i);
    return v;
}
uint32_t wifi_gen_pol_present(uint64_t t) { (void)t; return wifi_gen_vm->pol.present; }
uint32_t wifi_gen_pol_dma(uint64_t t) { (void)t; return wifi_gen_vm->pol.dma; }
uint64_t wifi_gen_pol_cfg_read(uint64_t t) { (void)t; return wifi_gen_vm->pol.cfg_read; }
uint64_t wifi_gen_pol_cfg_write(uint64_t t) { (void)t; return wifi_gen_vm->pol.cfg_write; }
uint32_t wifi_gen_pol_cmd_clear(uint64_t t) { (void)t; return wifi_gen_vm->pol.cmd_clear; }
uint32_t wifi_gen_pol_cmd_set(uint64_t t) { (void)t; return wifi_gen_vm->pol.cmd_set; }
uint32_t wifi_gen_pol_sinks(uint64_t t) { (void)t; return wifi_gen_vm->pol.sink_count; }
uint32_t wifi_gen_pol_sink(uint64_t t, uint32_t i) {
    (void)t;
    return i < wifi_gen_vm->pol.sink_count ? wifi_gen_vm->pol.sinks[i] : 0;
}
uint32_t wifi_gen_pol_descs(uint64_t t) { (void)t; return wifi_gen_vm->pol.desc_count; }
uint32_t wifi_gen_pol_desc_trb(uint64_t t, uint32_t k) {
    (void)t;
    return k < wifi_gen_vm->pol.desc_count ? wifi_gen_vm->pol.descs[k].trb : 0;
}
uint32_t wifi_gen_pol_desc_start(uint64_t t, uint32_t k) {
    (void)t;
    return k < wifi_gen_vm->pol.desc_count ? wifi_gen_vm->pol.descs[k].start : 0;
}
uint32_t wifi_gen_pol_desc_count(uint64_t t, uint32_t k) {
    (void)t;
    return k < wifi_gen_vm->pol.desc_count ? wifi_gen_vm->pol.descs[k].count : 0;
}
uint32_t wifi_gen_pol_desc_stride(uint64_t t, uint32_t k) {
    (void)t;
    return k < wifi_gen_vm->pol.desc_count ? wifi_gen_vm->pol.descs[k].stride : 0;
}

/* Control state. */
uint64_t wifi_gen_pc_ok(uint64_t t) { (void)t; return wifi_gen_vm->pc < wifi_gen_vm->n; }
uint64_t wifi_gen_fetch(uint64_t t, uint32_t i) {
    (void)t;
    if (wifi_gen_vm->pc >= wifi_gen_vm->n || i > 3) return 0;
    return wifi_le32(wifi_gen_vm->code_base + (uint64_t)wifi_gen_vm->pc * 16 + 4 * i);
}
uint64_t wifi_gen_advance(uint64_t t) {
    (void)t;
    wifi_gen_vm->pc++;
    wifi_gen_vm->steps++;
    return 0;
}
uint64_t wifi_gen_jump(uint64_t t, uint32_t target) {
    (void)t;
    wifi_gen_vm->pc = target;
    return 0;
}
uint64_t wifi_gen_stack_full(uint64_t t) { (void)t; return wifi_gen_vm->sp >= WIFI_STACK_DEPTH; }
uint64_t wifi_gen_stack_empty(uint64_t t) { (void)t; return wifi_gen_vm->sp == 0; }
/* The generated step calls these only when the stack is not full / empty. */
uint64_t wifi_gen_call(uint64_t t, uint32_t target) {
    (void)t;
    if (wifi_gen_vm->sp < WIFI_STACK_DEPTH) {
        wifi_gen_vm->stack[wifi_gen_vm->sp++] = wifi_gen_vm->pc;
        wifi_gen_vm->pc = target;
    }
    return 0;
}
uint64_t wifi_gen_ret(uint64_t t) {
    (void)t;
    if (wifi_gen_vm->sp) wifi_gen_vm->pc = wifi_gen_vm->stack[--wifi_gen_vm->sp];
    return 0;
}

/* Register file (Machine.reg / Machine.setReg: out-of-range is 0 / no-op). */
uint64_t wifi_gen_reg_get(uint64_t t, uint32_t r) { (void)t; return r < 16 ? wifi_gen_vm->r[r] : 0; }
uint64_t wifi_gen_reg_set(uint64_t t, uint32_t r, uint32_t v) {
    (void)t;
    if (r < 16) wifi_gen_vm->r[r] = v;
    return 0;
}

/* Scratch RAM (Sim.memLoad / Sim.memStore: bytes outside scratch read 0 and
   are not written). */
uint64_t wifi_gen_mem_load(uint64_t t, uint32_t at, uint32_t w) {
    (void)t;
    volatile uint8_t *const S = wifi_scratch;
    uint32_t v = 0;
    for (uint32_t i = 0; i < w; ++i)
        if ((uint64_t)at + i < WIFI_SCRATCH_BYTES)
            v |= (uint32_t)S[(uint64_t)at + i] << ((8 * i) % 32);
    return v;
}
uint64_t wifi_gen_mem_store(uint64_t t, uint32_t at, uint32_t w, uint32_t v) {
    (void)t;
    volatile uint8_t *const S = wifi_scratch;
    for (uint32_t i = 0; i < w; ++i)
        if ((uint64_t)at + i < WIFI_SCRATCH_BYTES)
            S[(uint64_t)at + i] = (uint8_t)(v >> ((8 * i) % 32));
    return 0;
}

/* Device effects. */
uint64_t wifi_gen_mmio_read32(uint64_t t, uint32_t off) { (void)t; WG_HOOKS; return WH_R32(off); }
uint64_t wifi_gen_mmio_read16(uint64_t t, uint32_t off) { (void)t; WG_HOOKS; return WH_R16(off); }
uint64_t wifi_gen_mmio_read8(uint64_t t, uint32_t off) { (void)t; WG_HOOKS; return WH_R8(off); }
uint64_t wifi_gen_mmio_write32(uint64_t t, uint32_t off, uint32_t v) {
    (void)t; WG_HOOKS; WH_W32(off, v); return 0;
}
uint64_t wifi_gen_mmio_write16(uint64_t t, uint32_t off, uint32_t v) {
    (void)t; WG_HOOKS; WH_W16(off, (uint16_t)v); return 0;
}
uint64_t wifi_gen_mmio_write8(uint64_t t, uint32_t off, uint32_t v) {
    (void)t; WG_HOOKS; WH_W8(off, (uint8_t)v); return 0;
}
uint64_t wifi_gen_cfg_read(uint64_t t, uint32_t off) { (void)t; WG_HOOKS; return WH_CR32(off); }
uint64_t wifi_gen_cfg_write(uint64_t t, uint32_t off, uint32_t v) {
    (void)t; WG_HOOKS; WH_CW32(off, v); return 0;
}
uint64_t wifi_gen_cfg_update(uint64_t t, uint32_t off, uint32_t clr, uint32_t set) {
    (void)t; WG_HOOKS; WH_CW32(off, (WH_CR32(off) & ~clr) | set); return 0;
}
uint64_t wifi_gen_phys(uint64_t t, uint32_t off) { (void)t; WG_HOOKS; return WH_PHYS(off); }
uint64_t wifi_gen_phys_base(uint64_t t) { (void)t; WG_HOOKS; return WH_PHYS(0); }
uint64_t wifi_gen_delay(uint64_t t, uint32_t us) { (void)t; WG_HOOKS; WH_DELAY(us); return 0; }
uint64_t wifi_gen_print(uint64_t t, uint32_t tag, uint32_t v) {
    (void)t; WG_HOOKS; WH_PRINT(tag, v); return 0;
}
uint64_t wifi_gen_done(uint64_t t, uint32_t st, uint32_t code) {
    (void)t;
    wifi_gen_status = st;
    wifi_gen_code = code;
    return st;
}

/* Run a started program with the generated step until it stops or the step
   count reaches `step_limit` (`Sim.resume`): the total steps since
   `wifi_start`. `code` receives the fail code, the yielded value or the
   offending pc. */
static int wifi_gen_resume(struct wifi_vm *vm, const struct wifi_hooks *h,
                           uint64_t step_limit, uint32_t *code) {
    wifi_gen_vm = vm;
    wifi_gen_h = h;
    while (vm->steps < step_limit) {
        wifi_gen_status = WIFI_GEN_NEXT;
        (void)leanos_device_program_step(0);
        uint32_t st = wifi_gen_status;
        if (st == WIFI_GEN_NEXT) continue;
        if (st == WIFI_HALT) *code = 0;
        else if (st == WIFI_FAIL || st == WIFI_YIELD) *code = wifi_gen_code;
        else if (st == WIFI_BAD_PC) *code = vm->pc;
        else *code = vm->pc - 1;
        return (int)st;
    }
    *code = vm->pc;
    return WIFI_STEP_LIMIT;
}

/* Start and run `image` to completion (programs that never yield); a yield
   ends the run with WIFI_YIELD. */
static inline int wifi_exec(const uint8_t *image, uint32_t image_len,
                            const struct wifi_hooks *h, uint64_t max_steps,
                            uint32_t *code) {
    static struct wifi_vm vm;
    if (wifi_start(&vm, image, image_len))
        return WIFI_BAD_IMAGE;
    return wifi_gen_resume(&vm, h, max_steps, code);
}

#endif
