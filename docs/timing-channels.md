# Timing channels

[ADR 0028](adr/0028-timing-channels.md) decides which timing differences
LeanOS closes, which it declares with their sources, and which are out of
scope. This page describes the two closures and the harness that measures the
paths the ADR names (issue #576).

## The closures

**Cross-subject refusals at a fixed budget (SC-TIMING-REFUSAL-BUDGET).** The
subject gate refuses a scheduled subject's request that names another subject
(ADR 0025). In the timing-channels image, the kernel decides the refusal with
the generated witness `leanos_cross_subject_refusal`
(`LeanOS.TimingChannels`). The witness reads three words:

- the latch mode (`1` when running);
- the scheduled subject plus one;
- the named subject plus one.

`TimingBudget.crossSubjectRefusal_agrees` proves that it answers exactly
`CompositeState.refusesCrossSubject`. A refusal returns `0xc5` after the
kernel has spun until 100000 cycles after entry. `TimingBudget.departure`
models that departure, and `refusal_fixed_budget` states the closure: two
states that agree on the mode and the scheduled subject refuse alike and
reply at the same cycle when the work fits the budget.

**No cycle counter at CPL3 (SC-TIMING-NO-USER-CLOCK).** `enable_smep` in
`boot/boot.S` sets CR4.TSD and clears CR4.PCE. The boot control check and
`validate_user_return` require both before any return to CPL3, and the
`CONTROL` record of every q35 image shows them (`cr4.tsd=1 cr4.pce=0`). RDTSC,
RDTSCP and RDPMC then fault at CPL3. `TimingBudget.userCounterFaults` states
that architectural reading as an assumption.

## The harness

The `timing-channels` q35 image (`LEANOS_TIMING_CHANNELS_SCENARIO`, on the
ipc-stream boot path) has two subjects:

- A, the observer;
- B, a receiver that blocks on endpoint 10.

A runs 64 rounds of the requests below (syscalls 110 to 115,
[userspace ABI](userspace-abi.md)), and the kernel reads the time-stamp
counter at CPL0 (`lfence; rdtsc`) around each:

| Record path | Class | What is timed |
| --- | --- | --- |
| `refusal.peer` | closed | A's request naming B, from entry to the padded departure |
| `refusal.unissued` | closed | A's request naming subject 9, never issued, likewise |
| `refusal.peer.work` | unpadded | The same refusal's work before the padding |
| `refusal.unissued.work` | unpadded | Likewise for subject 9 |
| `own-request` | baseline | A's request naming itself, which the witness passes; no padding |
| `copy-in.1` | declared | The SMAP copy-in window for 1 byte |
| `copy-in.16` | declared | The same for 16 bytes |
| `ipc.wake.idle` | declared | A's send waking B, to A's next entry; B blocks again at once |
| `ipc.wake.busy` | declared | The same, with B running 4096 iterations first |

After the rounds, A asks for the report (115). The kernel prints one record
per path:

```text
LEANOS/26 CYCLES path=refusal.peer class=closed samples=64 min=… median=… max=… budget=100000
```

It then prints the refusal overrun count and two transcript records: the
refusal record and the wake record. A executes RDTSC at CPL3. The #GP(0) is
bound to that instruction and recorded (`TSC-DENIAL`), and the image ends.

Switches between A and B are checked as in the ipc-stream image but not
recorded, because a record per switch would be serial output inside the
round trip being timed.

### Running it

```sh
./scripts/build-image.sh
LEANOS_BOOT_SCENARIO=timing-channels ./scripts/run-image.sh
```

`scripts/run-image.sh` compares everything except the `CYCLES` records with
`scripts/expectations/timing-channels.transcript`. It keeps those records in
`build/boot/timing-channels-cycles.txt` (`LEANOS_TIMING_CYCLES_ARTIFACT`) and
runs `scripts/report-timing-channels.py` on them. The report fails the run
when:

- a path is missing, out of order or malformed;
- a closed path's budget is not the image's;
- a refused reply left before its budget.

The report prints each path's median beside the median recorded in
`scripts/timing-channels-baseline.tsv`, with their ratio. It also prints:

- the spread between the two refusals' medians, padded and unpadded;
- the 16-byte against 1-byte copy difference;
- the busy against idle wake difference.

`--strict` also fails a median more than four times its baseline
(`--tolerance`) or any refusal overrun. Use it when comparing runs on one
machine. `--write-baseline REASON` records the run's medians, with a
`# reason:` line, as the new baseline.

### Reading the numbers

- **Closed.** The two refusal paths' medians sit at the budget, and their
  spread is close to zero, whatever the unpadded work's spread. An overrun is
  a refusal whose work exceeded the budget. It leaves when the work is done,
  so its departure is not fixed. The first refusal under TCG can overrun
  while QEMU translates the path.
- **Declared.** `copy-in.16` against `copy-in.1` shows the copy window's
  length dependence. `ipc.wake.busy` against `ipc.wake.idle` shows the
  receiver's run time inside the sender's round trip. Both are the sources
  ADR 0028 lists.
- **The clock.** Under QEMU's TCG the time-stamp counter follows the host's,
  so the counts move with host load. That is why the CI gate checks shape
  and the budget only. Under KVM, or on hardware, the counts are the CPU's
  cycles.

The recorded baseline comes from one local TCG run on a loaded host. In that
run:

- The padded refusals' medians were 100027 and 100021 cycles, a spread of
  0.0001. Their unpadded work differed: medians of 2402 cycles naming the peer
  and 268 naming subject 9, a spread of 0.89. The peer refusal is the first
  request of each round, right after the IPC round trip, so its work carries
  the state that round trip left behind. That is the kind of variation the
  padding hides.
- One refusal overran the budget, the first, while QEMU translated the path.
- The 1-byte and 16-byte copies were not told apart: the 16-byte median was
  2234 cycles lower, which is noise at this scale.
- The wake round trip with the receiver running 4096 iterations took 24122
  cycles longer at the median than with the receiver idle.

## On the Qotom

Not yet built. The q35 image cannot run on the Qotom: its platform admission
accepts only the q35 profile, and the Qotom's ring-3 path is the native
`qotom_entry_*` path, not `validate_user_return`. A Qotom timing run needs:

1. **A lab variant.** Add the timing-channels subjects and handler to the
   Qotom blocking-IPC integration build
   (`scripts/build-qotom-recovery-lab.py`, `LEANOS_QOTOM_BLOCKING_IPC_INTEGRATION`).
   Print the `CYCLES` records after the rounds, as on q35. The serial line
   runs at 38400 baud, so printing inside a timed path would dominate it.
2. **TSD on the native path.** Set CR4.TSD in the Qotom CR4 sequence, and
   extend `QotomNoSmapControl` and `scripts/audit-qotom-nosmap-control.py` to
   allow that bit. Until then the Qotom observer can still read the counter,
   and SC-TIMING-NO-USER-CLOCK does not cover the Qotom.
3. **A stable counter.** The J1900's time-stamp counter is invariant, so its
   counts are reference cycles. Record the firmware's C-state and
   burst-frequency settings with the capture, because both change how many
   reference cycles a path takes.
4. **A capture.** Run through `scripts/run-qotom-recovery-lab.py` as for the
   blocking-IPC integration. Then run `scripts/report-timing-channels.py
   --baseline <qotom baseline> --strict` on the extracted `CYCLES` records,
   and record a Qotom baseline with `--write-baseline`.
