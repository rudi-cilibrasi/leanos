# Historical physical watchdog arm rejection

The first timer trial rejected the GRUB SMI register value 20073 while expecting
only the earlier FreeBSD value 20033. It did not arm the timer and returned to
FreeBSD, whose boot epoch changed from 1788973888 to 1788978756. The raw trace
contains ARM-REJECTED followed by the FreeBSD chain marker; result.json records
recovery after 44.75 seconds. No immutable producer revision was retained for
this pre-commit trial, so it must not be attributed to the current recipe.

This is historical physical fallback evidence. The reviewed recipe later
admitted both observed SMI values, preserving that register, so this exact input
is no longer a rejection case. Current unknown-board/register rejection and
bad-request/load paths are covered by the GRUB/QEMU cases. The bytes here are
retained unchanged, with timestamped events and before/after boot observations.
