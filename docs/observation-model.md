# Observer-relative one-step isolation

`LeanOS.Observation` defines the first information-flow claim for the abstract,
sequential core. It is a scoped unwinding model, not a claim about the booted
binary or all kernel behavior.

## Claim vocabulary

An observer sees its live identity bit, capability slots and attenuated rights,
authorized byte contents, owned virtual-page permissions, syscall reply,
declared endpoint deliveries, and the current scheduler selection. Raw kernel
object and physical-frame identifiers are deliberately absent: a subject sees
only its local capability handle and the permissions relevant to its own view.

Two states are **low-equivalent** for a subject exactly when these complete
views are equal. A step is **silent** for that subject when its footprint cannot
change any component of the view. `silent_steps_lowEquiv` proves that two
independently chosen silent steps applied to low-equivalent states preserve low
equivalence; `silent_steps_equal_reply` additionally states equality of the
next visible reply. Thus secret-dependent high behavior need not choose the
same operation or arguments in both runs.

The supported operation classes mirror the deterministic sequential models:
map, unmap, access check, bounded copy, capability delegation and revocation,
typed rejection, endpoint send/receive, allocation, and scheduler selection.
The theorem covers unrelated private memory, mapping, access, copy, rejection,
receive, delegation, revocation, and sends whose sender and recipient are both
unrelated to the observer. The endpoint abstraction is capacity one: send
reports full without changing the queued delivery, and receive reports empty
or removes the unique delivery. It assumes
the trusted caller and active address space were selected by the kernel, as in
the syscall and user-copy models.

## Explicit channels and counterexamples

The kernel-reduced paired-state examples distinguish theorem scope from
channels:

- delegation into, or revocation from, the observer's capability slots is an
  authorized sharing channel;
- endpoint delivery to the observer is intentional declassification, including
  sender provenance and the two payload words;
- global allocation exhaustion can change a reply and is a resource channel;
- queue fullness changes the sender reply between `accepted` and `ipcFull` in
  the capacity-one abstraction and is demonstrated as a resource channel; and
- scheduler selection is explicitly visible, so scheduling differences are not
  silently abstracted away.

Shared-memory capabilities likewise end privacy: bytes and mappings authorized
to the observer belong in its low view. The model never claims confidentiality
for shared objects, endpoint messages, or these resource and scheduler channels.

## Scope and evidence

Lean proves the observer-relative projection theorem and equal-reply corollary.
Definitional-reduction examples evaluate paired states that differ only in
another subject's secret, exercise every modeled private operation class, and
demonstrate deliberate divergence through capability, IPC, resource-exhaustion,
and scheduler channels.
Existing modules separately prove authorization, state-preserving rejection,
mapping confinement, bounded-copy footprints, endpoint provenance, and
lifecycle cleanup; this module does not restate those integrity results as
confidentiality.

The claim is termination-insensitive, single-step, deterministic, and
sequential. It excludes timing, caches, speculation, probabilistic behavior,
SMP, covert-channel elimination, full trace equivalence, and liveness. Lean
compilation proves the model theorem only. The compiler, generated code, boot
assembly, QEMU, hardware, trusted entry context, and correspondence between this
unwinding model and the booted artifact remain trusted or unproved boundaries.
