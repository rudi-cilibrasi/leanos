# The boot dispatcher's memory-budget states, followed by the main kernel model

The boot dispatcher's memory-budget scenario was defined over a separate, smaller model of memory budgets. This section gives each of its states a meaning in the main kernel model, reached by the main model's own memory, scheduling, termination, and system-call steps, and shows that both models make the same decisions at every step.

- `runCommands_append` — Bookkeeping: replaying a list of scenario commands and then one more is the same as replaying the longer list.
- `paths_follow_edges` — Every step of the scenario's state graph extends its starting state's command list by exactly that command.
- `allStates_complete` — Bookkeeping: the list of scenario states is complete.
- `allCommands_complete` — Bookkeeping: the list of scenario commands is complete.
- `compositeOf_edge` — For every step of the scenario, the main model's state after it is the main model's counterpart step applied to the state before it.
- `views_agree` — At every scenario state, both models agree on which program is running, which programs are alive, and how much memory each living program uses and may use.
- `counterpart_matches_reply` — For every step of the scenario, the main model's counterpart step gives the same kind of answer: an allocation, a refusal for an exhausted budget, a switch, a termination, a refused stale handle, a release, or a refused repeated release.
- `budget_tokens_simulated` — Together: every scenario step is followed by the main model, with the same answer and the same budget view afterwards.
