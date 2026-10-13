# Oracle rows for the frame budget

The frame-budget scenario's rows on the stateful dispatcher: its canonical sequence and its hostile encodings.

- `malformed_budget_state_is_wrong_version` — The frame-budget row whose state word carries the wrong interface version is answered with the exact wrong-version rejection code, so a version error can never be misread as a legitimate budget-continuity failure.
- `hosted_budget_canonical_sequence` — The frame-budget scenario's canonical command sequence, run from its starting state, really does end in its completed state.
