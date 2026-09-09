# Qotom early-kernel watchdog recovery

Boot configuration source: bd72e93. The kernel image hash is recorded in
result.json, its checksum file, the GRUB load marker, and the post-recovery USB
readback. Exact installed GRUB files and kernel build provenance are retained.
The configuration was installed only after 24 GRUB/QEMU cases passed and its
files were compared byte for byte after sync, unmount, and read-only remount.

One dated, digest-bound request armed 120 watchdog ticks, loaded the kernel,
and reached its deliberate `cli; hlt` loop immediately after serial initialization,
before the normal BOOT record. The capture stayed quiet for 127.225990654 seconds.
A new GRUB boot appeared 128.011997919 seconds after arming, reported the request
consumed, and chained FreeBSD. Authenticated SSH returned with boot epoch
1788988719, changed from 1788987999. Read-only USB verification confirmed the
request remained consumed. No operator reset or BIOS change occurred.

The original in-memory runner parser rejected GRUB's wrapped SHA-256 load
message after recovery. The corrected parser accepts line breaks inside only
the exact expected digest and reclassified these unchanged bytes. Separate SSH,
USB identity, and consumed-state checks are in verification.txt. No extra boot
was performed. Settings: COM1, 38400 baud, 8N1, no flow control, FTDI/null modem.

This proves recovery for this explicit early-kernel stall. The consumed request
was durable, so the RTC expiry fallback was not exercised after this reset.
There is no LeanOS FINAL or normal-scenario success claim. The ordinary LeanOS
one-shot route still needs this watchdog protection and new normal-cycle
validation before the complete capture loop can be called unattended.
