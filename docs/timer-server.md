# Timer server

Issue #487 adds a ring-3 timer server over the one-shot PIT. The kernel keeps
the PIT, its programming, and the interrupt. The alarm policy (who may set
which alarms, and how many) belongs to a ring-3 subject that holds the timer
capability. Before this, only the `preemption` image used the PIT: it fires
twice, and every other image keeps the PIC fully masked.

## Design

- **The timer capability.** It is the authority to ask the kernel for one
  one-shot alarm with a count in `1 .. 65535`. That is the range of the 16-bit
  channel-0 counter. The bound leaves out 0, which the hardware reads as
  65536. Exactly one subject holds it: the timer server. An arm from any other
  subject is refused, and so is an arm outside the bound. Neither has any
  effect.
- **The kernel multiplexes the PIT.** The kernel keeps its own preemption
  deadline (ADR 0008) next to the server's alarm, and programs the earlier of
  the two. The server can only set its alarm. It cannot clear, delay or
  replace the preemption deadline.
- **Expiry.** When the alarm fires, the kernel masks IRQ0, acknowledges it,
  clears the alarm and signals the expiry notification bound to the holder's
  receive (the notification object of #471). The interrupt path touches
  nothing else: no client, no server state, no authority, and not the
  preemption deadline.
- **Clients.** A client reaches the server only through a send-only endpoint
  capability. The server's policy refuses a count outside the bound and a
  request that would give the client more than its quota of outstanding
  alarms. It queues the rest and arms the head alarm through its capability.
  On an expiry it signals the wake notification of the client whose alarm
  expired, and arms the next alarm.

## What is proved

`LeanOS/TimerServer.lean` models the split. Authority is static: one optional
timer-capability holder, and the set of subjects that hold the endpoint to the
server. The PIT state is the kernel's preemption deadline and the server's one
alarm. The server's state is its quota, the outstanding count per client, and
its queue of accepted alarms.

- **Only the holder arms the PIT.** `alarm_set_only_by_holder` says that a
  step that leaves an alarm armed either kept the old alarm, or was an
  accepted arm by the holder with a count in bound.
  `arm_non_holder_unchanged` and `arm_out_of_bound_unchanged` say that any
  other arm changes nothing.
- **Only the holder receives expiries.** `expire_delivered_to_holder` says
  the alarm interrupt is delivered only to the holder, and only while an alarm
  is armed. `ExpiryBound` (no other subject has pending expiry bits) is
  preserved by every step.
- **The kernel's interrupt path is unchanged in what it may touch.**
  `expire_footprint` lists everything the expiry leaves alone: authority,
  preemption deadline, server queue and counts, wakes and ticks. It changes
  only the alarm and the holder's expiry bits. `tick_footprint` says the
  preemption tick changes only the tick count.
- **The server cannot disable preemption.** `preemption_unchanged` holds for
  every operation, so `programmed_le_preemption` follows: the programmed count
  is never later than the kernel's deadline. `tick_independent_of_alarm` says
  the tick is accepted exactly when the kernel's deadline is set, whatever the
  server armed.
- **A client without the endpoint cannot set alarms.**
  `request_without_endpoint_unchanged` says such a request is refused with no
  effect. `QueueFromSenders` (every queued alarm, the only thing the server
  arms, comes from an endpoint holder) is preserved by every step.
- **Quotas.** `request_over_quota_refused` and
  `request_out_of_bound_unchanged` cover the server's refusals.
  `WithinQuota` (no client's outstanding count exceeds the quota) is preserved
  by every step.
- **Wakes.** `wake_only_by_holder` says a client's wake bits rise only when
  the holder collects an expiry and that client's alarm is at the head of the
  queue.

The stable claims are `SC-TIMER-CAPABILITY` and `SC-TIMER-SERVER-POLICY` in
[security-claims.md](security-claims.md). The negative fixture
`tests/negative/TimerExpiryToNonHolder.lean` checks that the capability claim
cannot be weakened so that an expiry also signals a subject without the timer
capability.

`boot_run` replays the boot image's script in the model:

1. B's arm and B's send are refused.
2. A asks for 65536 counts (out of bound, refused), then for 65535 (accepted).
3. C arms 65535.
4. A asks for another alarm. It is refused, because the quota is one.
5. The alarm expires and is delivered to C.
6. C wakes A, and A takes its wake bit.

The model has no time. Counts bound the hardware counter. They make no claim
about wall-clock accuracy, latency, drift, or timing channels. No wall clock,
APIC timer or TSC is involved.

## The generated witness

`timerServerDecide` (`leanos_timer_server_decide`, oracle adapter 27) is the
allocation-free lowering of the kernel's decisions on the boot authority.
`timerServerDecide_agrees` ties it to `step` on the boot system.

| Event | Arguments | Answer |
| --- | --- | --- |
| 0, arm | subject, count | 1 for C (3) with `1 <= count <= 65535`; `0x102` no timer capability; `0x202` out of bound |
| 1, send to the server | subject | 1 for A (1); `0x302` no endpoint |
| 2, alarm interrupt | word 1 when an alarm is armed | `0x304`, delivered to C; `0x702` not armed |
| 3, wake | signaller, client | 1 for C waking A; `0x502` not the holder |

Every other event is 0. `timerServerDecide_arm_accepts` proves, over every
64-bit input, that the witness accepts an arm only from C and only in bound.

## The `timer-server` scenario

The `timer-server` image is in the evidence tier, with the exact transcript
`scripts/expectations/timer-server.transcript`. It is the three-subject image,
with C built from `subjects/timer-server` by the [subject template](subjects.md).
At boot the kernel checks its read-only capability table against the witness:

- C alone holds the timer capability and the right to signal A's wake
  notification 13.
- A alone holds the send-only endpoint capability to endpoint 12.
- B holds nothing.

The run then goes like this:

1. C blocks receiving on endpoint 12.
2. B's arm (syscall 90) and its send (8) are refused. B reports both results
   and spins with interrupts enabled.
3. A, dispatched fresh, calls the server three times (8). C refuses 65536 as
   out of bound. It accepts 65535 and arms the one-shot PIT through its
   capability (90). It refuses a third request because of the quota. Each
   reply (91) resumes A.
4. A waits on its wake notification (93), and B's saved continuation runs.
5. The PIT interrupt arrives while B spins. The kernel masks IRQ0,
   acknowledges it, asks the witness, and wakes C's receive with the expiry
   bits. RCX is 0, meaning the expiry came from the kernel.
6. C wakes A (92) and blocks. A resumes with its wake bit and reports the
   three replies (94). The kernel checks them.

The kernel programs the PIT before it remaps the PIC. Mode 0 holds the output
low until terminal count, and the PIC initialization clears any edge latched
before it, so the only IRQ0 is the alarm's. The expiry has to arrive while B
spins. The alarm runs 65535 PIT ticks, about 55 ms, and the steps between the
arm and A's wait take far less. An expiry at any other point stops the
machine. It cannot pass silently.

Every other image is unchanged. In particular, `timer_handler` keeps its
preemption path, and the `preemption` image preprocesses exactly as before.
The scenario is integration evidence only. The C kernel, `boot.S`, the PIC/PIT
bridge (ADR 0005), the subject build, the compiler and QEMU stay trusted. The
server's policy is ring-3 code: the kernel checks only A's report of the
replies, not C's code against `policy`.
