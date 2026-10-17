# A loaded child's one message

This section is about the one thing a newly loaded child program does: send one message through the single message channel its parent gave it. It makes that send a step of the overall system model and shows that it can only put a message into that one channel's mailbox, that it changes nothing else, and that it keeps every safety and bookkeeping rule the rest of the proofs rely on.

- `childSend_shape` — A child's send either changes nothing and is not accepted, or it is accepted while the machine is running for a created child and publishes the new mailbox state.
- `childSend_unchanged` — Every send that is not accepted leaves the whole system unchanged.
- `endpointSend_accepted` — An accepted message send uses a live channel permission with the right to send, whose mailbox was empty, and fills exactly that mailbox.
- `childSend_sent` — An accepted send by the child puts exactly one message, from the child, into the empty mailbox of the channel named by the child's first permission slot, which allows sending.
- `childSend_confined` — An accepted send by the child changes no other mailbox, no permission, and nothing outside the message records.
- `send_capabilities_unchanged` — A message send never changes any permission.
- `send_preserves_occupied_mailbox` — A message send never touches a mailbox that already holds a message.
- `send_preserves_live_senders` — After a message send, every waiting message still comes from a live subject.
- `installSend_preserves_runtimeWellFormed` — Publishing any message send, whoever sends it, keeps the system's runtime safety rules.
- `childSend_preserves` — The child's send keeps the system's safety rules, its child bookkeeping rules, and its family-tree rules.
- `childSend_keeps` — The child's send changes no spawn record, frame ownership, memory, subject record, or permission.
