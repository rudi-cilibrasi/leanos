# Unarmed Qotom RTC preflight

One USB-first boot selected `rtc-probe`. GRUB reported 2026-09-09 20:51:15,
accepted the current-minute token, waited 65 seconds, then reported 20:52:20
and rejected the expired token. Timed serial events agree with UTC; FreeBSD
reports `machdep.wall_cmos_clock: 0`. FreeBSD SSH returned with boot epoch
1788987155 and the environment request was verified consumed.

The probe never armed the watchdog or booted LeanOS. This establishes RTC
convention and advancement during an ordinary GRUB boot, not across a watchdog
reset or after a hang. The failed armed trial remains unresolved.

The original runner had already loaded a parser that accepted LF/CRLF but not
GRUB's LF-CR line endings. It closed the capture after SSH recovery, then failed
classification. The corrected parser replayed these same unchanged bytes;
SSH, USB identity, clock configuration, configuration hashes and consumed state
were verified separately in `recovery-check.txt`. No extra boot was needed.

Raw serial uses COM1 at 38400 baud, 8N1, no flow control, via the FTDI/null-modem
link. The USB remains configured for FreeBSD by default; the unbounded watchdog
request is disabled. `result.json` records both installed configuration hashes.
