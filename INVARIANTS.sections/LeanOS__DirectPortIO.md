# Who may talk to hardware ports

The processor talks to simple devices, such as the serial console, the interrupt controller, and the timer, through numbered hardware ports. These theorems establish a strict door policy: a user program that tries to touch any port is always turned away without any device noticing, while the kernel itself may touch a port only when the exact port, direction, size, and stated purpose appear on a short reviewed list. Anything off that list is refused with the devices left exactly as they were.

- `selected_controls_deny_user_cpl` — Under the chosen processor settings, user-level code is never granted port access; the permission check comes out false.
- `selected_controls_allow_kernel_cpl` — Under those same settings, kernel-level code does pass the basic privilege check, so the reviewed list is what actually decides.
- `executeUser_total` — Bookkeeping: a user port request always produces some definite outcome; the handler can never get stuck.
- `executeKernel_total` — Bookkeeping: a kernel port request likewise always produces some definite outcome.
- `executeUser_deterministic` — The same user port request against the same state always gets the same outcome; there is no randomness or hidden state.
- `executeKernel_deterministic` — The same kernel port request against the same state always gets the same outcome; there is no randomness or hidden state.
- `user_request_preserves_device_state` — No user request, whatever port or value it names and however the checks turn out, ever changes any device's state by even one bit.
- `user_request_never_kernel_accepted` — A request arriving from user code can never come back stamped with the kernel-approved verdict; the two paths are provably separate.
- `accepted_user_request_denied_gp` — Under the accepted, freshly confirmed settings, a user port request has exactly one outcome: the modeled hardware protection fault, with everything else untouched.
- `kernel_acceptance_confined` — Whenever a kernel request is accepted, that acceptance certifies everything at once: the settings were the reviewed ones and freshly confirmed, kernel privilege held, the exact purpose-port-direction-size combination was on the reviewed list, the settings were left unchanged, and the devices changed only in the one prescribed way.
- `kernel_rejection_preserves_device_state` — Every refused kernel request is all-or-nothing: refusal leaves the complete device state exactly as it was.
- `byte_output_discards_upper_bits` — Sending a value too big for a one-byte port behaves exactly like sending the value with its extra bits dropped, matching what the real instruction does, so the extra bits can never smuggle information to a device.
- `directPortIODemo_selected_user_agrees` — A concrete worked example: on a user request under correct settings, the small numeric routine exported for the real build answers exactly as the full reference model does.
- `directPortIODemo_selected_kernel_agrees` — A concrete worked example: on an approved kernel serial-port write, the exported routine and the full reference model agree exactly.
- `directPortIODemo_rejection_agrees` — A concrete worked example: on a kernel request whose purpose does not match the port, both the exported routine and the reference model refuse in exactly the same way.
- `directPortIODemo_invalid_origin` — A request word naming a nonexistent origin is answered with the reserved invalid marker before anything else happens.
- `directPortIODemo_invalid_control` — A request word naming a nonexistent settings variant is likewise answered with the reserved invalid marker.
- `directPortIODemo_invalid_port` — A request naming a port outside the recognized set is likewise answered with the reserved invalid marker.
- `directPortIODemo_byte_normalization` — The exported routine drops oversized value bits exactly as the model does: writing a too-big value and writing its trimmed byte give identical results.
- `policy_nonvacuous` — The policy is demonstrated on a real case, not an empty one: one reviewed kernel write is genuinely accepted and changes only its own device's state, while the very same port and value words sent from user code are denied with every device untouched.
