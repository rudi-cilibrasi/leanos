# Finite scheduled observer isolation

`LeanOS.ScheduledObservation` composes the bounded scheduler with the observer
model and proves a termination-insensitive statement for finite prefixes. It
does not claim machine-code refinement.

## Exact claim and assumptions

The scheduler/lifecycle state is authoritative for the current subject and its
owned address space. Actor requests include claimed context solely to model a
stale adapter: execution succeeds only when the operation's actor, claimed
subject, scheduler current subject, and scheduler-derived owned address space
agree. `accepted_actor_uses_current_owned_space` proves that condition, while
executable regressions reject stale subjects and address spaces. The legacy
observation scheduler field is synchronized by one adapter, and
`sync_agrees` proves agreement.

`finite_trace_lowEquiv` applies to two low-equivalent starts and finite,
sequential runs whose declared low projections match. The runs may choose
different unrelated private writes, mappings, copies, rejections, and IPC
operations and may contain different numbers of silent steps. The conclusion
is equality of the complete final observer view. The projection includes a
post-step observer view for every non-silent transition, so it does not erase
visible replies or state, and retains every declared event. This is a supplied-public-schedule,
termination-insensitive result: it assumes neither fairness nor equal
termination, and says nothing about divergent infinite runs.

## Public channels and trusted boundaries

Scheduling selections, observer-directed capability transfer/revocation,
authorized shared-memory writes, observer endpoint delivery and provenance,
visible replies, allocation exhaustion, queue-full outcomes, kernel
rejections, and observed termination are public. Their projections must match;
the theorem deliberately does not hide them. Raw object/frame identifiers are
not added to the observer view, and user arguments cannot manufacture trusted
context.

Executable paired traces cover multiple dispatches and unequal silent-step
counts with different private writes, mappings, copies, rejections, and
unrelated IPC. Negative examples classify divergent public schedules, shared
writes, observer capability changes, endpoint delivery, resource outcomes,
queue fullness, and termination as projection differences or precondition
failures.

The proof is about the bounded Lean model. It does not prove that generated C,
assembly, the compiler, linker, QEMU, x86 hardware, the timer slice, or boot
transcripts refine this model. Kernel entry context and those implementation
boundaries remain trusted; successful compilation or QEMU execution is only
integration evidence.
