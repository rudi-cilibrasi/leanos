# Dated Qotom loader-stall watchdog trial

Source revision: 940662e8b0372e4be5636e9eded6d4967c30e656. One explicitly dated
watchdog request was generated from FreeBSD's UTC clock, consumed by GRUB, and
accepted by the current-minute guard. The exact board/register contract passed
and armed 120 TCO ticks. GRUB then deliberately slept with a 300-second software
escape; that escape was not reached.

After 128.764685829 seconds from the arm marker, the new GRUB boot reported
`DEFAULT request=none` and chained FreeBSD. Authenticated SSH returned with boot
epoch 1788987999, changed from 1788987155. Read-only USB inspection verified the
request remained consumed. No BIOS change or operator reset occurred in this
trial. COM1 used 38400 baud, 8N1, no flow control over the FTDI/null-modem link.

This passes the deliberately stalled loader recovery case. The consumed request
was durable in this run, so the dated-token expiry fallback was not exercised
after the reset. This does not explain the earlier unbounded trial's repeated
requests, prove all reset mechanisms durable, or establish kernel-hang recovery.
The existing lab ELF hash in result.json is the runner's media identity check;
this loader-stall trial did not launch that ELF or produce a LeanOS FINAL record.

The installed configuration, guard, and register recipe were compared byte for
byte after a sync, unmount, and read-only remount before the trial. Their exact
bytes and hashes are retained here alongside unmodified serial bytes and timed
events. The USB remains FreeBSD-default with the unbounded watchdog-test request
disabled, and was unmounted after the consumed-state verification.
