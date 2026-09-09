# Qotom watchdog investigation (#333)

Completed-run recovery is implemented; unattended loader/kernel hang recovery
is still unverified. This investigation establishes the actual starting state
for a boot-stage watchdog implementation. It does not arm the timer or change
the USB, firmware, or canonical kernel.

## Observed FreeBSD state

On 2026-09-09, the installed FreeBSD 15.0 system was still on boot epoch
1788973888 following the recorded completed-run cycles. No `ichwd` module was
loaded. The read-only probe compiled on that machine with
`cc -Wall -Wextra -Werror -O2` and produced:

```text
host=0f008086 lpc=0f1c8086 acpi=00000403 pbase=fed03002
pmc=00000010 no_reboot=1 smi_en=00020033 tco_smi=0
tco1_cnt=0800 halted=1 locked=0 timer=0004 reload=0004 status1=0000 status2=0000
```

The timer is halted and unlocked. PMC reset inhibition is set. TCO SMI
handling is disabled. No timeout status was observed. These are register
observations, not evidence that a watchdog reset will survive firmware and
return to FreeBSD.

The [probe](../hardware/lab/qotom-watchdog-probe.c) uses FreeBSD `PCIOCREAD`,
read-only PMC mapping, and input port instructions. It checks the exact
observed host/LPC identities and enabled base-register values before reading
MMIO or ports. It has no arming operation and no register writes. FreeBSD
requires write-open permission on `/dev/pci` for this ioctl and on `/dev/io`
for the port-access grant; the actual operations remain reads.

Run on the reference FreeBSD host:

```sh
cc -Wall -Wextra -Werror -O2 qotom-watchdog-probe.c -o qotom-watchdog-probe
sudo ./qotom-watchdog-probe
```

## Driver-derived constraints on the next implementation

Primary sources are FreeBSD's
[ichwd.c](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/dev/ichwd/ichwd.c)
and [ichwd.h](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/dev/ichwd/ichwd.h).
The Bay Trail device `8086:0f1c` uses TCO version 3. The driver derives ACPI
ports from LPC PCI offset `0x40`, PMC memory from offset `0x44`, and the
NO_REBOOT register from PMC base plus eight. TCO lives at ACPI base plus
`0x60`; version 3 uses one-second ticks.

Crucially, `device_shutdown` calls `ichwd_detach`, which stops an active timer.
Thus arming FreeBSD's normal watchdog and then issuing an ordinary SSH reboot
is not a demonstrated way to protect the subsequent GRUB/LeanOS boot. The
boot path must arm after shutdown, or an independently supported reset
controller must supervise it.

The driver also clears NO_REBOOT with readback and disables TCO SMI handling
because firmware handlers can reload or disable the timer. Timer enable/disable
preserves only the documented control bit, status clearing uses separate
write-one-to-clear operations, and changing the timeout requires a reload.
Do not replace these operations with blind full-register constants derived
only from this one snapshot.

## Remaining execution and validation

Add an opt-in boot-stage arm operation after successful consumption of the
one-shot request, before image loading. Check identities and decode, preserve
unrelated control state, verify reset enable and timeout readback, and reject
arming failures before handing control to an experiment. A load failure must
stop the armed watchdog before normal FreeBSD fallback. An unarmed boot must
not alter watchdog state.

Retain separate tests for a deliberate loader-stage hang and an early kernel
hang, with timestamped serial capture, a bounded expected reset interval,
consumed request, changed FreeBSD boot identity and authenticated SSH recovery.
Test ordinary completion and failed-arm fallback as well. Timer expiration is
recovery evidence only; it must never turn an incomplete LeanOS trace into a
successful scenario. Until those physical tests pass, the existing runner's
`hang_recovery: false` remains accurate.

## Physical timer trial: reset works, recovery fails

An opt-in GRUB timer experiment at source `e3863f8` armed 120 TCO v3 ticks
only after validating the board and register state. Its initial trial rejected
GRUB's SMI register `0x20073` (FreeBSD had reported `0x20033`) and returned to
FreeBSD. The next trial admitted those two observed states, preserving SMI_EN.
Seven actual GRUB/QEMU tests passed before that physical trial.

The physical trace then repeated SELECT and WATCHDOG-ARMED at approximately
13.34, 141.80 and 269.82 seconds. The timer reset the board before the 300-second
software escape, but the same request loaded again despite the earlier
`save_env` success. This **fails unattended recovery**. The cause of repeated
persistent state is not yet established; it must not be described as a proven
USB cache or firmware defect. The ordinary CF9 reset's successful cycles do
not establish durability across this watchdog reset.

The watchdog-test path is now disabled in the template: it falls back to
FreeBSD without arming. The register recipe is retained only for investigation.
The already installed experimental configuration needs replacement after
physical USB removal allows FreeBSD to boot. No further watchdog arm is
appropriate until independent durable one-shot consumption is demonstrated
under the actual reset mechanism. A GRUB success message or a same-boot cached
readback alone is insufficient.

The bounded [failed observation](../hardware/lab/observations/qotom-watchdog-20260909/result.json) retains all 420 seconds of serial events and the failure classification. The post-disable seven-case GRUB/QEMU suite passes, including watchdog-disabled fallback.

## Candidate independent expiry guard

`grub-qotom-watchdog-window.cfg` is a candidate guard, not sourced by the active
lab configuration. A request names exactly one RTC minute using unpadded
`watchdog-test-YEAR-MONTH-DAY-HOUR-MINUTE` fields. It rejects a different minute,
implausible clock, or inconsistent resampling across rollover. The 120-tick
watchdog interval exceeds the maximum 60-second eligibility window, so an
advancing RTC would reject the old request after the observed reset even if
USB state repeats. This complements durable consumption; it does not prove it.

GRUB's [datehook implementation](https://github.com/rhboot/grub2/blob/master/grub-core/hook/datehook.c)
reads the clock on variable access and formats these values as unpadded decimal
integers. An arm producer must use the same RTC convention and allow enough of
the selected minute for the loader to reach the guard. It must not broaden the
window on failure or silently use the observing host's wall clock.

The 14-case actual GRUB/QEMU suite passes: seven existing boot/fallback cases
plus current-minute acceptance, stale replay of the same token two minutes
later, future minute, wrong date, missing expiry, malformed padding, and invalid
clock rejection. The clock fixtures never arm a watchdog. Before enabling this
path physically, establish the Qotom RTC convention and advancement, verify
stale-token rejection across its watchdog reset, and complete the deliberate
loader/kernel hang recovery tests. A stopped or backward-jumping RTC remains
outside this proposed guard's guarantee and must be recorded as a trust
assumption or addressed with a separate recovery mechanism.
