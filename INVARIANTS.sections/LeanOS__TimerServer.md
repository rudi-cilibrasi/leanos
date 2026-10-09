# A timer server program that owns alarm policy, while the kernel keeps the timer hardware

The kernel keeps the machine's one-shot hardware timer and the interrupt it raises; a separate, ordinary program, the timer server, decides which alarms to set. Exactly one program holds the "timer permission" that lets it ask the kernel to set the timer, and only for a count within the hardware's range. Other programs ask the server for alarms through a message connection; the server refuses requests that are out of range or would give a program more than its allowed number of pending alarms, and wakes a program when its alarm goes off. These theorems guarantee that only the permission holder can set the timer or hear it go off, that the kernel's own preemption timer can never be switched off or delayed by the server, that the kernel's interrupt handling touches nothing beyond the alarm and the server's notification, that a program without the connection cannot get an alarm set, and that no program ever has more pending alarms than its allowance. They say nothing about how accurate the timer is in real time.

- `arm_non_holder_unchanged` — A request to set the timer from a program without the timer permission is refused and changes nothing.
- `arm_out_of_bound_unchanged` — A request to set the timer for a count outside the allowed range changes nothing and is not accepted.
- `arm_accepted` — When a request to set the timer is accepted, it came from the permission holder with a count in range, and the timer now holds exactly that alarm next to the unchanged preemption deadline.
- `alarm_set_only_by_holder` — Any alarm the timer holds after a step was either already there or was just set by the permission holder with a count in range.
- `preemption_unchanged` — No step, including anything the timer server does, changes the kernel's own preemption deadline.
- `programmed_le_preemption` — Whatever alarm the server has set, the time the kernel actually programs into the hardware is never later than its own preemption deadline.
- `tick_independent_of_alarm` — Whether the kernel's preemption tick is accepted does not depend on any alarm the server has set.
- `tick_footprint` — The kernel's preemption tick changes nothing except the count of ticks taken.
- `expire_footprint` — When the alarm goes off, the kernel's interrupt handling changes only the alarm and the permission holder's notification: permissions, the preemption deadline, the server's queue and counts, wake-ups and the tick count are all untouched, and no other program's notification changes.
- `expire_delivered_to_holder` — An alarm going off is delivered only to the timer-permission holder, only while an alarm is set, and clears the alarm.
- `step_preserves_auth` — No step changes who holds the timer permission or who has a connection to the server.
- `step_preserves_expiryBound` — Only the permission holder ever has an alarm notification waiting, and every step keeps it that way.
- `expiry_only_to_holder` — No step ever changes the alarm notifications of a program that does not hold the timer permission.
- `request_without_endpoint_unchanged` — An alarm request from a program without a connection to the server is refused and changes nothing.
- `request_out_of_bound_unchanged` — An alarm request for a count outside the allowed range is refused and changes nothing.
- `step_preserves_queueFromSenders` — Every alarm waiting in the server's queue, the only alarms it ever sets, belongs to a program that has a connection to the server, and every step keeps it that way.
- `step_preserves_withinQuota` — No program ever has more pending alarms than the server's per-program allowance, and every step keeps it that way.
- `request_over_quota_refused` — A request that would give a program more pending alarms than its allowance is refused and changes nothing.
- `wake_only_by_holder` — A program is woken only when the timer-permission holder collects a fired alarm and that program's alarm is first in the queue.
- `bootSystem_invariants` — The starting setup of the demonstration machine satisfies all three rules: no stray alarm notifications, no queued alarm from an unconnected program, and no program over its allowance.
- `boot_run` — The demonstration run gives exactly the expected answers: the unauthorized program's timer request and server request are refused, the client's out-of-range request is refused, its next request is accepted and the server sets the timer, its second request is refused for exceeding the allowance, the alarm reaches the server, the server wakes the client, and the client collects its wake-up.
- `kernelSend_refused_iff` — The kernel refuses a program's message to the server exactly when the full model refuses that program's alarm request for lacking a connection.
- `timerServerDecide_agrees` — The small numeric checker the running kernel consults gives exactly the model's answers for timer requests at and around the allowed range from each program, for messages to the server from each program, for the alarm going off with and without an alarm set, and for wake-ups.
- `timerServerDecide_arm_accepts` — For every possible input, the checker accepts a timer request only from the timer server and only for a count from 1 to 65535.
- `timerServerDecide_send_accepts` — For every possible input, the checker lets only the client program send to the server.
