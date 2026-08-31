# Simple mailboxes with permission checks

This file models the simplest form of message passing: each meeting point (endpoint) has a one-message mailbox, sending never puts anyone to sleep, and every operation demands the right permission. The theorems guarantee that only programs holding a genuine, current permission can send or receive; that every message in a mailbox truly came from an accepted send and carries its sender's real identity; and that destroying a meeting point wipes both its mail and every permission for it, everywhere, at once.

- `revokeSubtree_preserves_wellFormed` — Taking back a whole family of passed-on endpoint permissions keeps every record consistent.
- `revokeSubtree_preserves_noncapability_state` — Such a take-back touches only permissions: memory records, mailboxes, and the send history are all left exactly as they were.
- `revokeSubtree_rejected_unchanged` — A refused family take-back changes nothing.
- `create_rejected_unchanged` — A refused attempt to create a new meeting point changes nothing.
- `destroy_rejected_unchanged` — A refused destruction changes nothing.
- `send_rejected_unchanged` — A refused send changes nothing.
- `receive_rejected_unchanged` — A refused receive changes nothing.
- `create_preserves_wellFormed` — Creating a meeting point, whether accepted or refused, keeps every record consistent.
- `send_preserves_wellFormed` — Every send keeps every record consistent.
- `receive_preserves_wellFormed` — Every receive keeps every record consistent.
- `destroy_preserves_wellFormed` — Every destruction keeps every record consistent.
- `accepted_send_authorized` — A send is accepted only when the caller genuinely holds a current send permission for a meeting point.
- `delivered_receive_authorized` — A message is handed over only to a caller genuinely holding a current receive permission.
- `accepted_send_records_caller` — The sender's name written into a message is the caller's true identity as known to the kernel; nothing in the message content can forge it.
- `reachable_mailbox_has_accepted_send` — In any state the system can actually reach, every message sitting in a mailbox got there through a real, accepted send at some earlier moment — messages cannot appear out of nowhere.
- `delivered_has_send_provenance` — Every delivered message traces back to the accepted send that created it, and the sender name it carries is that sender's true identity.
- `destroy_clears` — Destroying a meeting point empties its mailbox, retires its identity, and leaves no program anywhere still holding a permission for it.
- `delegate_no_authority_amplification` — Sharing a permission with another program can never create a right the giver did not already have.
