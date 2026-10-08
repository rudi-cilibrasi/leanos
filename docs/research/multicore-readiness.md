# Research: what a second application processor would require

Status: decision draft for issue #500. No code, model change or AP startup is
proposed here.

## Decision

**Stay single-core.** Do not start AP startup, per-CPU state or a lock model
until three things exist:

1. the single-export refinement method of ADR 0023 has been applied to more
   than one export, so that it is known whether per-CPU scalar adapters can be
   refined the same way;
2. the composite state has been split by footprint (#499), so that adding
   per-CPU fields does not force every proof to be replayed; and
3. explicit spawn (#489) exists, so that the subject lifecycle that concurrency
   must protect has its final shape.

When those hold, the first concurrent step should be **a big-kernel-lock (BKL)
interleaving model**, not fine-grained locking. It is the only step whose proof
cost can be bounded from the current sequential theorems.

## Current evidence

- A multi-vCPU boot is rejected before CPL3.
  - `BootTopology` reports `Error.multipleEnabledProcessors`, which the
    generated MADT stream encodes as error 75.
  - The kernel stops with `@7/BOOTALLOC@ status=FAIL
    reason=topology-madt-generated-entries`.
  - Claim SC-SINGLE-CORE-BOOT-ADMISSION covers this.
  - The `multivcpu-rejection` scenario boots `-smp 2,sockets=1,cores=2,threads=1`
    and checks the QMP inventory ([boot-image.md](../boot-image.md)).
- Every model is sequential. `KernelTransition` says so explicitly. `Scheduler`,
  `SubjectLifecycle` and `FailStop.CompositeState` have exactly one `current`
  subject, and `TLB.State` has one `active` address space.

## What the composite state would have to add

| Area | Today | Needed for a second processor |
| --- | --- | --- |
| Current subject | `lifecycle.current : Option SubjectId` | One per CPU, plus the invariant that no subject runs on two CPUs |
| Entry stacks and TSS | One guarded entry stack and IST set (ADR 0015) | Per-CPU stacks, TSS and IST, and the entry-stack gate extended per CPU |
| Address space and TLB | `TLB.State.active`, one cached entry list | Per-CPU `active` and caches, and a shootdown protocol so that unmap and revoke complete only after every CPU has invalidated (today's `InvalidationPublication` orders publication on one CPU) |
| Interrupt state | One IF/PIC/PIT model, vector-32 gate | LAPIC per CPU, IOAPIC routing, IPIs for shootdown and rescheduling |
| IPC and capabilities | Single atomic transitions | Atomicity across CPUs: a lock model (BKL first) or a linearizable interleaving semantics |
| Boot | BSP only; APs are never started | INIT/SIPI, AP admission against the platform profile, per-AP control normalization |
| Device programs | The executor runs inside one syscall | Exclusive executor ownership per device, or a lock |

## Which theorems survive

**Under a BKL interleaving**, every kernel transition runs with the lock held,
so the sequential step theorems remain true *per step*. What changes is the
glue that composes steps:

- *Survive as stated:* single-transition theorems over model state, such as
  `Capability.copy_no_authority_amplification` (SC-CAP-AUTH), the
  well-formedness preservation family (SC-KERNEL-WF, the composite `*-WF`
  claims), `BlockingIPC.keyCycle_delivers`, and the IOMMU model theorems. These are about one
  atomic step, and a BKL makes kernel steps atomic.
- *Need restatement:* theorems that quantify over "the current subject" or
  "the active address space" (scheduler, preemption, user-return confinement,
  page-fault provenance, stale-translation invalidation). They must become
  per-CPU, and gain an invariant that relates the per-CPU states.
- *Need new proofs:* anything that relies on the absence of a concurrent
  observer: TLB shootdown completion before frame reuse, the
  `ScheduledObservation` isolation trace (SC-SCHEDULED-ISOLATION, which assumes
  one global schedule), and the frame-budget and scrub ordering.

**Under fine-grained concurrency**, no current theorem survives without a
linearizability argument for its operation, and the composite gate theorems
would need a rely-guarantee or concurrent-layer framework that the repository
does not have.

## How comparable projects handled it

- **CertiKOS** extended its certified-layer methodology to concurrency
  (certified concurrent abstraction layers, OSDI 2016). The concurrency
  layers, per-CPU and shared-object logs, and the linearization of every
  shared primitive dominated the proof effort. That is the cautionary point:
  concurrency was a framework rewrite, not an increment.
- **seL4** is verified for its single-core configuration. Its SMP
  configuration, which uses a big kernel lock, is shipped but not covered by
  the functional-correctness proof. The *clustered multikernel* approach
  (von Tessin) instead runs one verified single-core kernel instance per core
  and lifts the single-core proof to a multikernel with a small additional
  argument about the shared lock and memory partitioning. That is the closest
  analogue to the BKL-first plan above.

## Exit

This draft closes #500. Any AP-startup or per-CPU modelling work is a new
issue that must cite this decision and show the three preconditions above.
