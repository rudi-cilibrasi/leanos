# Timer interrupts and the one-shot program switch

These theorems cover the moment a hardware timer fires and the kernel decides whether to switch which program is running. They guarantee that a switched-off timer changes nothing, that at most one timer event is ever honored in this one-shot design, that the scheduler's bookkeeping stays sound through the event, and that the program handed the processor is chosen by the scheduler alone — never by values sitting in the interrupted program's registers.

- `masked_tick_unchanged` — Whenever the timer is switched off, a timer event changes nothing: the kernel's state stays exactly as it was and no program is dispatched.
- `accepted_tick_is_unique` — Whenever a timer event actually dispatches a program, it is the one and only such event: afterwards exactly one tick has been accepted and the timer is disarmed, so a second tick can never be honored.
- `preserves_scheduler_wellFormed` — No matter how a timer event is handled — accepted, rejected, or ignored — the scheduler's internal bookkeeping rules still hold afterwards.
- `accepted_context_comes_from_scheduler` — Any program dispatched by a timer event was chosen by the scheduler's own step, running in its own address space; the interrupt's saved registers play no part in the choice.
- `preemptionDemo_agrees` — The small stand-alone demo routine exported for the boot demonstration gives exactly the same answer as the full model on the worked two-program example.
