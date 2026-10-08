# Who may write to and read from the console

These theorems model the first service program planned for LeanOS: a console server. Three programs share one console. Only the server holds the *console permission*, the right to print bytes and to read typed bytes. One client holds a send-only connection to the server, and a third program holds neither. The model asks what that third program can do to the console and what it can learn from it. The permissions are fixed for the whole run: this model has no way to hand a permission over. The kernel's own diagnostic messages are a separate channel and are not covered.

- `step_unprivileged_state` — Every operation attempted by a program that holds neither the console permission nor a connection to the server is refused and leaves the console, the server's message queue and the unread input exactly as they were.
- `step_unprivileged_delivery` — Such a program gets back exactly one answer for each attempt: a refusal.
- `console_integrity` — Deleting every action of such a program from a run does not change the final state at all, including everything printed on the console.
- `console_integrity_pair` — Two runs that differ only in what such a program does print exactly the same thing on the console.
- `step_preserves_noQueuedFrom` — If no message from a given unprivileged program is waiting at the server, none ever will be, whoever acts next.
- `step_observations_other` — When another program acts, an unprivileged program receives nothing, as long as none of its messages is waiting at the server.
- `unprivileged_observations` — Everything an unprivileged program ever receives is one refusal per attempt of its own, and nothing else.
- `console_confidentiality` — What an unprivileged program receives is the same whatever was typed on the console, so it cannot learn any console input.
- `bootAuthority_b_unprivileged` — In the permission layout the console image is meant to install, the third program holds neither the console permission nor a connection to the server.
- `demo_output` — In the demonstration run, the client sends 42, the third program tries to print and to send, and the server serves: the console shows exactly 42.
- `demo_b_refused` — In that run, both of the third program's attempts are refused.
- `demo_a_accepted` — In that run, the client's message is accepted and the server's acknowledgement reaches it.
