# Leaks that need another program to run

These theorems show the leaks whose demonstration needs program 1 to run between two timer switches. The kernel's own evaluator runs the example traces on the standard sample boot plan, the same plan the hosted dispatcher replays from, and checks every concrete fact at once. In the first pair of runs, the observer sees the same permissions and the same sealed permission waiting on its endpoint, but that permission's hidden history differs. Revoking a permission tree, either the observer's own or program 1's, then cancels the waiting permission in one run and not the other. In the other pairs, program 1 has saved different register contents, and the answers to the observer's timer switch, its blocking send that wakes program 1, and its cancellation of program 1's wait carry those registers.

- `facts_sample` — The kernel's evaluator confirms every concrete fact about the example runs on the standard sample boot plan.
- `sample_plan_exists` — The standard sample boot plan compiles.
- `facts_of_compile` — For the compiled sample plan, every concrete fact holds.
- `restoreBlockingPeer_virtualMemory` — Handing the processor to a waiting program's peer never changes the virtual-memory state.
- `dispatchBlockingReceive_virtualMemory` — A blocking receive never changes the virtual-memory state.
- `switch_translations_virtual` — A context switch never changes the memory view recorded in the page-translation state.
- `keepsSpaces_step` — Permission copies, offers, context switches and blocking receives never change address-space owners or mappings in a healthy state.
- `keepsSpaces_run` — A whole run of such operations keeps address-space owners and mappings.
- `lowEquiv_of_viewData` — Two states that agree on the checkable part of the observer's view, on address-space owners and on mappings are indistinguishable.
- `runFrom_wellFormed` — Every run from the example state ends in a healthy state.
- `ownStepCounter_of_pairFacts` — Two such runs whose checkable facts agree meet every condition of the privacy theorems.
- `leftTrace_keeps` — The first run uses only operations that keep address-space owners and mappings.
- `rightTrace_keeps` — The second run uses only such operations.
- `preemptLeftTrace_keeps` — The first switching run uses only such operations.
- `preemptRightTrace_keeps` — The second switching run uses only such operations.
- `blockedTrace_keeps` — The runs that park program 1 use only such operations.
- `facts_parts` — Bookkeeping: the combined check splits into its named facts.
- `derivation_pair` — The two runs with different hidden permission histories meet every condition of the privacy theorems.
- `blocked_pair` — The two runs that park program 1 with different registers meet every condition.
- `not_lowEquiv_of_pending` — If the sealed permission waiting on the observer's endpoint differs, the observer can tell the states apart.
- `revokeSubtree_own_step_inconsistent` — Revoking the permission tree at the observer's own slot gives distinguishable results, because a hidden history decides whether the waiting permission belongs to the tree.
- `revokeSubtree_other_step_inconsistent` — Revoking the permission tree at program 1's root gives distinguishable results for the same reason.
- `resumePreempt_output_inconsistent` — The answer to the observer's timer switch carries program 1's saved registers, so it differs between the states.
- `blockingSend_output_inconsistent` — The answer to the observer's send that wakes program 1 carries program 1's saved registers.
- `blockingCancel_output_inconsistent` — The answer to the observer cancelling program 1's wait carries program 1's saved registers.
