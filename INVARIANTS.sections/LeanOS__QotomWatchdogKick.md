# Long WiFi test runs on the lab machine stay under the safety timer

The lab machine boots LeanOS under a hardware safety timer: the boot loader starts a two-minute countdown, and if LeanOS hangs the timer resets the machine, which then returns to its normal operating system. To watch the WiFi network change its broadcast key, a test run has to last much longer than two minutes. In a long run the kernel restarts the countdown, but only while the WiFi driver keeps making progress: once when the connection comes up, and then after every forty one-second progress marks from the driver. Each restart is decided by a small generated checker. These theorems describe that checker and show that it allows a restart only under exactly those conditions, never when the timer was not started by the boot loader or its timeout was changed, never more often than the run's fixed allowance (and never more than 92 times for any run), at least forty progress marks apart, and that the machine is therefore always reset within a bounded time — at most about three hours for the longest allowed run — no matter what LeanOS does.

- `capKicks_eq` — The largest allowance of timer restarts, that of a one-hour run, is 92.
- `budget_1800` — A thirty-minute run is allowed 47 timer restarts.
- `budgetOf_le_cap` — Any run of at most an hour gets an allowance no larger than the one-hour run's.
- `budget_le_iff` — The checker's built-in allowance limit, written as a plain machine number, is exactly the one-hour run's allowance of 92.
- `ticks_ge_iff` — The checker's built-in spacing of forty progress marks, written as a plain machine number, is exactly the model's restart spacing.
- `kickDecide_zero_iff` — The checker allows a restart exactly when the run's allowance is valid and not used up, the timer is still running with the boot loader's two-minute timeout, and the event is either the connection coming up (for the first restart) or a progress mark after at least forty marks since the last restart.
- `unarmed_never_kicked` — If the timer is not running as the boot loader left it, the checker never allows a restart.
- `changed_never_kicked` — If the timer's timeout is no longer the boot loader's two minutes, the checker never allows a restart.
- `step_kicks` — Handling one driver record never takes the number of restarts past the run's allowance.
- `run_kicks_le_budget` — However the driver behaves, a run restarts the timer at most its allowance's number of times.
- `step_kicks_mono` — The count of restarts never goes down.
- `run_kicks_le_cap` — Whatever allowance an image declares, a run restarts the timer at most 92 times, because a larger allowance is refused outright.
- `kick_needs_ticks` — Every restart other than the one when the connection comes up follows at least forty progress marks since the previous restart.
- `deadline_le` — If each restart happens before the countdown then running expires, the final deadline is at most two minutes per restart after the starting deadline.
- `reset_bound` — Counting from the boot loader starting the timer, a run with a given number of on-time restarts is reset no later than two minutes times one more than that number.
- `cap_reset_seconds` — With the largest allowance, the machine is reset no later than 11160 seconds (about three hours) after the boot loader starts the timer.
- `session_1800_reset_seconds` — For a thirty-minute run, the machine is reset no later than 5760 seconds (96 minutes) after the boot loader starts the timer.
