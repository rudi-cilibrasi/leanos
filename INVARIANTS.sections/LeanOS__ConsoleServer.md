# Who may write to and read from the console

These theorems model the first service program of LeanOS: a console server, which the `console-server` boot image runs. Three programs share one console. Only the server holds the *console permission*, the right to print bytes and to read typed bytes. One client holds a send-only connection to the server, and a third program holds neither. The model asks what that third program can do to the console and what it can learn from it. The permissions are fixed for the whole run: this model has no way to hand a permission over. The kernel's own diagnostic messages are a separate channel and are not covered. The later theorems tie the model to the boot image: the booted kernel checks each permission decision against a small decision function proved equal to the model's, and the image's run is replayed in the model.

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
- `step_of_not_permitted` — A request that the permission layout does not allow is refused and changes nothing.
- `step_write_of_permitted` — A console write that the layout allows adds exactly its one byte to what the console shows.
- `unprivileged_not_permitted` — A program that holds neither the console permission nor a connection to the server is allowed no operation at all.
- `consoleAuthorize_agrees` — The small numeric decision function that the booted kernel calls gives, for every program and every operation, exactly the model's answer for the console image's permission layout: accept when the layout allows it, refuse otherwise.
- `consoleAuthorize_off_domain` — Asked about an operation number or a program number outside the agreed codes, that decision function answers neither accept nor refuse.
- `consoleAuthorize_accepts` — That decision function says accept only to the server for console operations and to the client for sending.
- `boot_output` — In the run that the console-server boot image performs, the console shows exactly `hello`, a newline, `world`, a newline.
- `boot_b_refused` — In that run, the program without permissions has all three of its attempts refused.
- `boot_a_observations` — In that run, the client's attempt to print directly is refused and both of its messages are accepted.
- `boot_server_receives` — In that run, the server's console read finds no input, and its receives alternate between finding nothing waiting and receiving the client's two messages in order.
