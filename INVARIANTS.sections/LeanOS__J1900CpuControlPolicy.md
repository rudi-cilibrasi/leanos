# Qotom J1900 CPU and control checkpoint

The composed policy accepts only when the supplied processor snapshot matches the measured J1900 profile and all eight fast-entry registers match their expected complete values. Its result is a bounded status record; it neither performs the hardware reads nor permits entry to user mode.

- `acceptance_iff` — The policy accepts exactly when both the measured J1900 CPU selector and the complete Intel fast-entry register check accept their supplied values.
- `query_never_authorizes_cpl3` — The policy always leaves its user-mode authority word clear, including after successful CPU and register checks.
