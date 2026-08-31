# The front door for sending and receiving messages

This is the public doorway through which programs send and receive simple two-word messages. The caller's identity is trusted kernel context, and the meeting point (endpoint) is named by a coded number that must match a live, current permission held by that caller. The theorems guarantee that every request either performs its operation properly or is refused with nothing changed, and that messages move only for the true caller holding the right permission — never for an identity or permission conjured out of the request's numbers.

- `dispatch_preserves_wellFormed` — Every send or receive request through this door keeps both the memory records and the message records consistent.
- `dispatch_sendHandleRejected_unchanged` — A send refused because its endpoint number was malformed or out of date changes nothing.
- `dispatch_receiveHandleRejected_unchanged` — A receive refused for the same reason changes nothing.
- `dispatch_sendRejected_unchanged` — A send refused by the mailbox layer — missing permission, full mailbox, and so on — changes nothing.
- `dispatch_receiveRejected_unchanged` — A receive refused by the mailbox layer — missing permission, empty mailbox, and so on — changes nothing.
- `accepted_send_uses_trusted_caller` — A send goes through only when the kernel-established caller, not anything written in the request, genuinely holds send permission.
- `delivered_receive_uses_trusted_caller` — A message is handed over only when the kernel-established caller genuinely holds receive permission.
- `accepted_send_resolves_exact` — Every accepted send first verified the supplied number against a real, live endpoint permission of the current generation in the caller's own permission book.
- `delivered_receive_resolves_exact` — Every delivered receive passed exactly the same verification of its supplied number.
- `ipcDemo_agrees_with_endpoint_scenario` — The compact demo used by the boot test gives the same answers as the real model on the reviewed two-program handoff: wrong-direction attempts are refused and the delivered message carries the true sender.
