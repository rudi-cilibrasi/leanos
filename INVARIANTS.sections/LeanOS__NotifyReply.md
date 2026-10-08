# Notifications and one-shot reply permissions

Two small kernel objects let programs cooperate without trusting each other. A *notification* is a word of signal bits: a program allowed to signal it sets bits without ever waiting, and a program allowed to wait on it collects the pending bits or waits until some arrive. A *reply permission* is created by the kernel when one program calls another: the called program gets the right to answer that one caller exactly once, and nothing else. These theorems guarantee that neither object hands anyone extra authority, that an answer to a caller who has since ended (or whose identity was reused) is refused, that each reply permission works only once and can never be passed on, and that one program's use of them cannot disturb another program's resources.

- `non_cap_step_caps` — Signalling, waiting, calling, replying, attempting to pass on a reply permission, and ending a program never change the ordinary permission records, so every guarantee already proved about permissions still applies.
- `reply_created_only_by_call` — A reply permission only ever comes into existence when a program calls another, and it names exactly that caller as it was at the moment of the call.
- `stale_reply_rejected` — A reply to a caller that has ended, or whose identity has moved on to a newer generation, is refused and changes nothing.
- `reply_single_use` — Answering consumes the reply permission: a second answer through it is refused and changes nothing.
- `copyReply_rejected` — A reply permission can never be handed to another program; every attempt is refused and changes nothing.
- `call_exhausted_unchanged` — When the called program has no free reply slot left, the call is refused with a clear reason and nothing changes.
- `signal_without_send_rejected` — A program that may only wait on a notification cannot signal it; the attempt is refused and changes nothing.
- `replies_change_only_at_server` — The only operations that touch a program's reply slots are a call to that program's endpoint and that program's own reply; no one else's activity can use up or clear them.
- `notifyReplyEvent_agrees` — The small numeric checker the running kernel consults at each step of the boot demonstration gives exactly the answers the model itself produces, for both the normal sequence and the refused cases.
- `notifyReplyEvent_unknown_zero` — The checker answers zero, a value no real answer uses, for anything outside its two scripted sequences.
