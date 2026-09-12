# Qotom RTL8168E-VL bus-master gating

The retained Realtek observation reports the same stopped-state candidate for
both 10ec:8168 endpoints: TXCFG `2f900d00`, Command `00`, interrupt mask
`0000`, receive configuration `0002ff0e`, Command `00`, and TXCFG `2f900d00`
(hexadecimal). The Command samples have TX enable, RX enable and reset clear;
TXCFG's hardware-revision field identifies RTL8168E-VL and its queue-empty bit
is set. This permits a bounded BME-clear candidate without running the active
FreeBSD stop sequence or acknowledging pending interrupt status.

The helper accepts only an exact prior stopped-state observation, successful
prior root-port BME result, exact endpoint/root routing and capability binding.
It collects the full routed endpoint state again, requires that it remains
stopped and exactly matches the retained prior sample, then reads Command 0007.
It attempts one 16-bit Command 0003 write, checks immediate readback, collects
the full routed state with endpoint Command 0003, and checks Command once more.
The second state must remain stopped and equal to the prior sample.

Two 90-read routed collections and three Command reads total 183 reads. There
is exactly one endpoint configuration write. Memory and I/O decoding and the
adjacent PCI Status halfword are retained. Failed writes may have effects, so
the attempt and observed readback are retained without retry or rollback. The
first failed read stops.

Statuses are 0 success, 1 argument, 2 prior state/route, 3 initial refresh,
4 changed stopped state, 5 Command, 6 write, 7 immediate readback and 8 final
state/readback. Output before the write is zero; ambiguous write failures retain
the attempt and prior Command. This helper does not write the endpoint engine,
interrupt mask or status registers, reset the device, poll, or invoke the
FreeBSD driver's timeout-logging stop path.

Ordinary tests cover both endpoints, exact 183-read order, every failed read,
all prior state bits, changes in every state sample before and after the write,
ignored and failed writes with and without effect, early Command drift, immediate
readback failure and final BME reassertion. The existing routed-state tests cover
the complete bridge header/PCIe mutations and invalid route/prior bindings.

This establishes only a bounded candidate for retaining the observed disabled
TX/RX engines while gating new endpoint memory/I/O requests through BME. The
queue-empty and Transactions Pending samples are sequential. They do not prove
that all earlier transactions completed, exclude later firmware/AP/device
activity, establish system-wide DMA containment or admit the Qotom platform.
Native emission, decoder tests and physical validation remain outstanding. The
consumed word-store authority is described below.

## Consumed word-store authority

The writer admits only bus 1 or 3, device/function zero, Command offset 4 and
value 0003. Every request consumes the armed flag, including a rejected request.
It maps only that endpoint's ECAM page as supervisor, writable, NX and UC,
performs one 16-bit store, restores the exact saved leaf, invalidates and checks
controls before returning. Mapping, restoration or control interference is
terminal. Failed stores may still have effects.

Arming first revokes all prior authority and bus selection. It binds the exact
endpoint, corresponding bridge route, successful root-port transition, prior
stopped state, copied firmware and active root/control state. The existing root
checker rejects every present ECAM alias. The gate publishes the endpoint bus
only after all checks and performs no hardware access.

Window tests cover both buses, reuse, every invalid field and word value,
missing callbacks, invalid apertures, failed stores, exact restoration and all
terminal interference paths. Arming tests cover both endpoints, every one of
4096 page-table positions aliasing either target ECAM page, endpoint header
bits, route results, prior statuses, firmware/root/control changes, missing
callbacks and rejected rearm. No store or invalidation occurs during arming.
