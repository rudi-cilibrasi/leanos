# Qotom terminal invalid-opcode checkpoint

The opt-in Qotom exception image extends the closed-root CPL3 entry checkpoint
with one real synchronous exception. It is an intermediate hardware experiment,
not a production exception dispatcher or a passing blocking-IPC image.

Build it with all of the Qotom admission prerequisites and both final options:

```text
--copy-root-publication --entry-integration --exception-integration
```

The first two CPL3 entries use `int 0x80`. The first returns a fixed value and
the user code checks that value plus the other fourteen saved registers. The
second entry emits the existing `QOTOM-ENTRY` record, changes saved RAX to a
second fixed value, and returns through the audited closed-root primitive. User
code checks that value and executes `UD2` at one linked address.

Vector 6 is terminal. Its assembly stub disables maskable interrupts, records
the incoming root, reloads the published closed root, reads CR3 back, requires
the incoming root to equal the selected subject root, and then checks the
hardware frame:

- RIP is the linked `qotom_entry_user_exception` instruction;
- CS is the user code selector `0x23`;
- RSP is the exact user A stack top and SS is `0x1b`;
- RFLAGS has bit 1 and the fault-class RF image bit set, while TF, IF, DF,
  IOPL, NT, VM, AC, VIF, VIP and ID are clear.

The success path emits `!C6` directly through COM1 and enters an absorbing halt
loop. `C` means that root closure, readback and the exact frame checks passed.
An unclosed root emits `!U6`; a closed root with a wrong frame emits `!E6`.
Neither terminal path calls C or returns.

The linked audit checks the exact instruction shapes, operands, targets, user
trap address and absence of calls/returns in the terminal path. Its self-test
builds both entry variants and rejects mutations to the root close, frame,
flags, user-return check and trap.

The capture decoder accepts exactly one final `!C6` after the entry manifest,
direct-port control, readiness and successful entry record. It rejects a
structured `FINAL` in this deliberately terminal experiment. The protected
runner still requires the expected ELF hash, the watchdog launch, 30 to 100
seconds of silence after the marker, automatic FreeBSD recovery and a consumed
one-shot request. The exception-specific upper bound accommodates a complete
autonomous watchdog expiry; the existing entry-stage bound remains unchanged.
The decoder projects the earlier records back through the
entry and copy-root decoders so all prerequisite observations remain checked.

This checkpoint demonstrates one synchronous CPL3 `#UD` delivery on the named
Qotom image and a fail-stop closed-root terminal. It does not authorize
recoverable exception dispatch, timer or external-interrupt routing, enable IF,
run blocking IPC, establish liveness, or emit `FINAL PASS`.
