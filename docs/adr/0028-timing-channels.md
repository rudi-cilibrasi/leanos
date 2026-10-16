# ADR 0028: Timing channels are declared, closed or out of scope

- Status: Accepted, issue #576
- Date: 2026-10-16

## Context

SC-COMPOSITE-OBSERVER-ISOLATION (#479, #551–#553) covers every request a
scheduled subject makes through the subject gate. Its only exclusions are the
ones #479 allows, and the first of them is timing: the claim is about what a
request returns and what it changes, not about when it returns.

The timing differences are real:

- a send that wakes a blocked receiver switches to it, and the sender resumes
  only after the receiver blocks again;
- the SMAP copy window takes time in proportion to the bytes it copies;
- device programs run for a bounded number of steps per invocation;
- every kernel path takes time that depends on what it reads.

A subject can measure these differences only with a clock. Before this ADR
every q35 image left CR4.TSD clear, so RDTSC and RDTSCP worked at CPL3, and
CR4.PCE was inherited from the firmware. The other clocks a subject can build
are coarser:

- counting its own instructions between two preemptions (images with a
  preemption tick);
- watching the order in which subjects run, which the scheduler decides and
  which the claim already treats as a public input;
- a device register read through a device program, which only the device's
  holder can run.

LeanOS runs subjects on one CPU, so there is no concurrently running subject
that could count while the observer's request is in the kernel.

## Decision

Every timing difference falls into exactly one of three classes. The
timing-channels image measures the paths this ADR names
([timing channels](../timing-channels.md)).

### Closed by construction

Each closed channel has a claim row and a contract theorem.

1. **Cross-subject refusals leave at a fixed budget**
   (SC-TIMING-REFUSAL-BUDGET). The subject gate (ADR 0025) refuses a
   scheduled subject's request that names another subject.
   - The decision reads three words every observer sees: the latch mode, the
     scheduled subject and the subject the request names. The boot witness
     `leanos_cross_subject_refusal` (`LeanOS.TimingChannels`, oracle adapter
     34) takes exactly those words and answers exactly
     `CompositeState.refusesCrossSubject` on them
     (`TimingBudget.crossSubjectRefusal_agrees`). It has no other input, so
     the refusal cannot read anything of the target.
   - The reply is padded: the kernel spins until a fixed budget of cycles
     after entry. Two refusals whose work fits the budget leave at the same
     cycle, and none leaves before it (`TimingBudget.departure_fixed`,
     `departure_not_early`). The padding costs one budget per refusal, which
     a subject pays only for a request that cannot succeed.
   - Together (`TimingBudget.refusal_fixed_budget`): states that agree on the
     mode and the scheduled subject refuse the same request with the same
     result, change nothing, and reply at the same cycle, whatever the
     target's liveness, issuance, slots or wait state.
   - No other image gives ring 3 a request that names another subject
     (ADR 0025). The timing-channels image is the one boot path that does,
     and it implements both parts: the witness decides, and the kernel pads.
     Any later syscall that exposes such a request takes the same path.
2. **CPL3 has no cycle counter** (SC-TIMING-NO-USER-CLOCK). `enable_smep`
   sets CR4.TSD and clears CR4.PCE with SMEP and SMAP. The boot control check
   and the validated user return (`validate_user_return`, the only path to
   `iretq` in the q35 images) require TSD set and PCE clear
   (`TimingBudget.userReturnClockControls`). Under the architectural reading
   of RDTSC, RDTSCP and RDPMC (`TimingBudget.userCounterFaults`, an
   assumption about the processor) each faults at CPL3
   (`TimingBudget.clock_controls_deny_user_counters`). This closes the clock
   that every other timing channel needs, down to the coarse clocks listed
   above.

### Declared, with their sources

A declared difference is real and stays. Each one has its source listed,
which says what it can reveal and to whom.

| Path | What varies | Source | Why declared |
| --- | --- | --- | --- |
| A send on an endpoint (`ipc.wake.*`) | Whether the sender resumes at once or after the receiver runs and blocks again, and how long the receiver runs | The waiter state of an endpoint the sender holds a capability to, which is in its view (`CompositeObservation.observe`), and the receiver's run time | The receiver is the party the sender talks to and can tell it anything through the reply; the scheduling handoff is the point of blocking IPC |
| The SMAP copy window (`copy-in.*`) | Time in proportion to the bytes copied | The length the caller passes, and the caller's own pages | Only the caller's own arguments enter |
| Device programs | The time a program waits on its device, within its invocation's step budget | The device and the program, both held by the device's holder | Only the holder invokes the program (ADR 0022); the step budget bounds what anyone else waits |
| The scheduler | When the next subject runs, the preemption tick, the cost of a switch | The ready queue and the saved-context bank (`KernelPublic`) | Already a declared public input of SC-COMPOSITE-OBSERVER-ISOLATION |
| Every other kernel path, including rejections and the nested-transfer refusal | Whatever the path reads | Each path reads the caller's arguments and its own authority; the generated witnesses read only the words the kernel passes them | The reply is a function of the full view (`CompositeFullIsolation.full_output`), but the C path's time is not proved to be; each path's inputs are listed in its own document |
| Evidence images' serial records | The time to print a record | The record, which the scenario fixes | Diagnostic output of the evidence images, not kernel policy |

### Out of scope

- Microarchitectural state: caches, TLBs, branch predictors, prefetchers,
  store buffers, speculative and transient execution.
- Physical channels: power, electromagnetic, thermal and acoustic.
- Firmware and platform timing: SMM, the Intel TXE, bus and DMA contention,
  device interrupt timing.
- The host under QEMU and KVM.
- The Lean model's own evaluation cost: no model carries time.
- The termination channel, which SC-COMPOSITE-OBSERVER-ISOLATION already
  excludes.

The padding of closed channel 1 does not change this scope. It also hides
microarchitectural variation along the refusal path, but no claim says so.

## Measurement

The `timing-channels` q35 image is the harness. Subject A, the observer, runs
64 rounds of every named path, and the kernel reads the time-stamp counter at
CPL0 around each one:

- the two closed refusals, naming the live peer and a subject never issued,
  with their padded departure and their unpadded work;
- the observer's request naming itself, as an unpadded baseline;
- the copy window for 1 and 16 bytes;
- the wake round trip with the receiver idle and with it running 4096
  iterations.

Each path is reported as one record with its minimum, median and maximum. The
runner keeps the records out of the exact transcript, because counts vary
from run to run. `scripts/report-timing-channels.py` checks their shape and
that no refused reply left before its budget, and prints each median against
`scripts/timing-channels-baseline.tsv`. Its `--strict` mode fails a median
above four times the baseline, or a refusal overrun. The image then executes
RDTSC at CPL3 and records the #GP(0).

On the Qotom the procedure is documented but not yet built
([timing channels](../timing-channels.md#on-the-qotom)).

## Consequences

- **The cost of the padding.** The kernel spins inside the entry, with
  interrupts masked, so each refused request delays interrupt delivery by up
  to its budget. The image's budget of 100000 cycles is sized for TCG, where
  the first refusal also pays for QEMU's translation. A kernel that refuses
  cross-subject requests outside this image would set its budget from the
  refusal path's measured worst case plus a margin, and would count overruns
  in the same way.
- **Transcripts.** Every q35 image's `CONTROL` record gains
  `cr4.tsd=1 cr4.pce=0`. It is spelled once, in
  `scripts/expectation-template.sh`.
- **Subjects.** RDTSC, RDTSCP and RDPMC fault at CPL3. No subject used them.
  A subject that needs time must ask a server for it, as the timer server's
  clients do.
- **The Qotom.** The native Qotom return path keeps its own reviewed CR4
  sequence (`QotomNoSmapControl`) and does not set TSD yet. Adding it needs a
  lab run, so it is left to a follow-up. Until then SC-TIMING-NO-USER-CLOCK
  is a claim about the q35 images only.
- **Refinement.** Neither closure is a refinement claim. The padding loop,
  the CR4 writes and the `validate_user_return` check are hand-written C and
  assembly that the claims trust.
- **ABI.** Syscalls 110 to 115 exist only in the timing-channels image
  ([userspace ABI](../userspace-abi.md)). No dispatcher table changes. The
  oracle corpus gains adapter 34 and its 10 vectors (702 in all).
