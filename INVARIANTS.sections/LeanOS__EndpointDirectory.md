# How a name service hands out connections without handing out more power

These theorems model a directory program: a name service that lets one program find another. A server program registers a name, a single 64-bit number, by passing the directory a copy of its connection permission (an *endpoint* permission). A client asks the directory for a name, and the directory answers with a copy of that permission that it has weakened itself, so the client may only send to the server, never receive its messages, pass the permission on, or take it away. All copying goes through the same capability rules as the rest of the system. The theorems say that a directory that weakens its answers to "send only" can never give anyone more power than the directory itself had, and that asking for an unknown name gets a clearly labelled "not found" answer that changes nothing. The last theorems tie the model to the `endpoint-directory` boot image, whose kernel checks each of the directory's answers against a small decision function proved equal to the model's.

- `sendOnly_attenuates` — The directory's own policy, offering only the right to send, counts as weakening to send-only.
- `copy_accepted_shape` — Whenever a permission copy succeeds, the copier really held the original permission, that permission included the right to pass it on, the copied rights are a subset of the original's and suit the kind of object, and the only slot that changed is the one that received the new copy, which names the same object.
- `rightsValid_of_attenuates` — A set of rights that is at most "send" can only be valid for a connection (endpoint) object, never for memory or for an address space.
- `resolve_unregistered` — Asking the directory for a name nobody registered gets the "unregistered" answer and leaves every permission in the system exactly as it was.
- `resolve_miss_unchanged` — Whenever the directory's answer is any kind of "not found" or refusal, no permission anywhere has changed: nothing was handed over.
- `resolve_resolved_held` — When the directory does answer with a permission, it is a copy of the very permission the directory holds under that name: same object, a connection, with exactly the offered rights, which are no more than the directory's own and no more than "send", and the directory's permission allowed passing it on.
- `resolve_no_amplification` — After the directory answers, every power any program has either existed before, or is the client's new right to send to a connection on which the directory itself could already send and pass the permission on.
- `resolve_only_send` — Asking the directory never gives any program the right to receive, to pass a permission on, to take one away, to read or to write, unless it already had it.
- `resolve_new_authority_held` — Any power a program newly gains from the directory is one the directory itself already had: the directory cannot hand out what it does not hold.
- `resolve_preserves_wellFormed` — Asking the directory keeps the whole permission system's bookkeeping consistent.
- `register_duplicate_unchanged` — Registering a name that is already registered is refused as a duplicate and changes nothing.
- `register_accepted` — After a successful registration, the name leads to the directory slot that now holds a copy of the server's permission, weakened to "send and pass on", and those rights were within what the server held.
- `resolve_delivered` — When the directory answers with a permission, its rights are exactly what the model's rights rule allows for the directory's own rights: "send" when the directory can both send and pass on, nothing otherwise.
- `directoryResolve_agrees` — The small numeric decision function that the booted kernel calls gives, for every combination of connection rights the directory might hold, exactly the model's rights rule.
- `directoryResolve_unregistered` — For a name that is not registered, that decision function always answers "unregistered", whatever rights are involved.
- `directoryResolve_no_amplification` — That decision function never answers with any rights other than "send", and answers "send" only when the directory's rights include both sending and passing on.
- `boot_registered` — In the run that the boot image performs, the server's registration of the name ECHO succeeds.
- `boot_resolved` — In that run, the client's request for ECHO is answered with a permission in its slot 1.
- `boot_missed` — In that run, the client's request for the unregistered name NONE gets the "unregistered" answer and changes nothing.
- `boot_client_capability` — In that run, the permission the client receives is a send-only connection to the server's endpoint 14.
- `boot_witness` — The decision function answers "send" for the rights the directory holds in that run, and "unregistered" for the missing name.
