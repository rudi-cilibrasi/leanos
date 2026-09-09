# Completed-run recovery after disabling the watchdog trial

The Qotom was found running FreeBSD again with boot epoch 1788983566. The cause
of recovery from the earlier repeating watchdog trial is unknown. The attached
USB (serial 11758C40, capacity 62914560000) still held the enabled trial config,
but its request was already `none`.

After backing up the existing config, the tested configuration that disables
`watchdog-test` was installed, synced, unmounted, remounted read-only, and compared
byte for byte. Its SHA-256 was
`447a820ffb572d726bf4e44a42ad548f608c64bba844f6110981b076ac0fa496`.
The USB was unmounted after verification.

One normal lab cycle then passed without manual BIOS intervention. It selected
the existing lab ELF (SHA-256 in result.json), emitted the expected
`dma-identity` rejection, stayed quiet for 34.260742347 seconds, reset through
the completed-run path, and chained to FreeBSD. SSH returned with boot epoch
1788986204, and the request was verified consumed. Serial settings were COM1,
38400 baud, 8N1, no flow control, through the FTDI/null-modem cable.

The raw serial bytes and timestamped events are retained without editing.
The failed `hd0,gpt2` probe is the USB candidate; the subsequent successful
FreeBSD chain marker identifies `hd1`. These are observations from the same
run, not assertions that disk numbering is stable.

This verifies completed-run recovery with the restored configuration. No
watchdog was armed in this run; it does not establish early-hang recovery or
explain the previous repeating requests. The RTC expiry guard remains untested
on hardware.
