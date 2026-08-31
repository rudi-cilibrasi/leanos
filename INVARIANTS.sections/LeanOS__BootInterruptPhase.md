# Who handles interrupts during boot

An interrupt is a hardware signal — a device demanding attention, or the CPU reporting a fault — that forcibly diverts the processor to a handler. During boot the kernel moves through a fixed sequence of interrupt-handling regimes: the arrangement inherited from firmware, two bootstrap stages, and finally the full runtime setup, plus a locked "halted" state that records why boot stopped. These theorems guarantee that this sequence only ever moves forward, that any interrupt arriving too early halts the machine safely with a recorded reason instead of being mishandled, and that none of this early machinery can touch the kernel's real working data or switch on the permission to run ordinary programs.

- `contract_table` — Every kernel-owned stage claims ownership of interrupt line 2 (the non-maskable interrupt), only the final runtime stage may ever authorize returning control to an ordinary program, and the old narrow descriptor format never survives into the 64-bit stages.
- `step_total` — Bookkeeping: every possible operation in every state produces some definite result; the model never gets stuck without an answer.
- `step_deterministic` — Bookkeeping: the same operation applied to the same state always produces the identical result.
- `publish_preserves_business` — Publishing an interrupt table never reads or changes the kernel's separate working data.
- `dispatch_preserves_business` — Handling an interrupt event never reads or changes the kernel's separate working data.
- `step_preserves_business` — Combining the previous two facts: no boot-interrupt transition of any kind touches the kernel's working data.
- `step_never_arms_return_authority` — No boot-interrupt transition can ever switch on the permission to return control to an ordinary program.
- `owned_bootstrap_event_terminal` — Whenever an interrupt arrives during either bootstrap stage, the machine immediately locks into the halted state carrying a record of exactly what happened, and nothing else changes.
- `dispatch_never_advances_publication` — An interrupt event can never push boot forward a stage: the machine either stays where it is or drops into the halted state.
- `early_event_never_delegated` — Before the runtime interrupt table is in place, no event is ever passed along to an ordinary interrupt handler.
- `Phase.rank_le_four` — Bookkeeping: the numeric position assigned to each stage never exceeds four, the position of the halted state.
- `publish_monotonic` — Publishing tables only ever moves the boot sequence forward; nothing moves backward, and the firmware-inherited table is never reloaded.
- `inherited_unreachable` — Once the kernel owns interrupt handling, no operation can ever hand it back to the firmware-inherited arrangement.
- `published_is_exact_successor` — An accepted publication is always exactly one forward step along the fixed chain — firmware-inherited to first bootstrap, first to second bootstrap, or second bootstrap to runtime — and the final step happens only with every runtime prerequisite genuinely in place.
- `runtime_requires_prerequisites` — The runtime interrupt table cannot be published until its task record, its dedicated emergency stacks, and its reviewed list of handlers all exist.
- `runtime_defers_to_runtime_contract` — Once the runtime stage is reached, events are passed along untouched to the separately proved runtime rules; this model neither replaces nor weakens them.
- `runtime_vector2_contract_unchanged` — The runtime handler this model names for interrupt line 2 is the same reviewed halt-only handler proved elsewhere, and it never appears among the ordinary handlers.
- `terminal_absorbing` — Once the machine has locked into the halted state, every further operation is absorbed and the original halt record is kept unchanged.
- `terminal_suffix_absorbing` — Absorption holds not just for one operation but for any finite sequence of them: after halting, nothing ever changes again.
- `owned_bootstrap_event_terminal_absorbing` — Putting the pieces together: an interrupt during a bootstrap stage halts the machine with its record, and from then on every further operation is absorbed, the kernel's working data stays exactly as it was, and the permission to enter ordinary programs stays off.
- `orderly_publication_witness` — A worked example showing the intended path really exists: performing the three publications in order reaches the runtime stage with no halt, untouched working data, and return permission still off.
- `bootstrap_event_witnesses` — Concrete examples showing the halt rules are not empty promises: a non-maskable interrupt in the first bootstrap stage and a fault in the second both genuinely lock in the expected halt record while preserving the working data.
- `bootPhaseModelExpected_total` — Bookkeeping: the fixed-width encoding used to replay this model against the generated boot code produces a definite answer for every possible input.
