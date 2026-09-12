# AHCI port capture retry — 2026-09-11

The operator reported a reset and requested another capture. SSH was reachable
before this protected retry. The installed AHCI port image was reused; no image
or USB configuration update preceded this run.

The result again reported status 0, CMD `6` before and after, IE `0`, TFD `50`,
SSTS `123`, SACT `0` and CI `0` (hexadecimal). The terminal remained
`qotom-platform-pending`. This repeats the observations; it does not establish
transaction drain, continuing firmware/AP exclusion or full boot admission.

FreeBSD recovered after 34.301236186001915 seconds of serial quiet,
boot time 1789170960 to 1789173880, with the request consumed.
Independent SSH verified the installed image and GRUB hashes and request=none;
the read-only mount was removed afterward. Serial was COM1 via FTDI/null modem,
38400 baud, 8N1.

ELF SHA256: `f15d68953a4179897c7b9a075135c722a538e84c77d25bd4561eeba65e810a67`.
The [original capture](../qotom-native-ahci-port-20260911/README.md) retains the
clean build at 1543c35 and guarded installation provenance. This retry ran at
170842f with unchanged runner/decoder code. The new interrupt-disable helper at
that revision was not part of the installed image and did not execute here.
