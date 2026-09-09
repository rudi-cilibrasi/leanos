# Qotom recovery acceptance audit (#333)

This audit covers the current lab rejection image on the reference Qotom with
legacy USB first. It does not admit Qotom to CPL3 or claim canonical halt evidence.
The implementation and physical checks are complete; repository merge admission
must still pass on the final PR head.

| Requirement | Evidence |
| --- | --- |
| Persistent FreeBSD default and explicitly armed USB boot | The [arrangement](qotom-boot-recovery-lab.md) identifies the internal boot partition by UUID. Every protected cycle records the consumed-request default and successful chain. |
| Consume before kernel handoff; bind selected image | [GRUB template](../hardware/lab/grub-qotom.cfg.in) saves request=none before expiry/arm/load; the request includes the configured digest, the runner checks the installed ELF, and GRUB checks its checksum file. |
| Idempotent state and failure fallback | Environment replacement writes one request; repeated request=none disarms it. GRUB/QEMU tests cover invalid environment state, unknown and expired requests, wrong digests, missing guard/recipe, rejected arming, bad checksum and bad ELF. Hash/load failures call timer stop before fallback. |
| Completion mode with an observation interval | The lab overlay retains the exact rejection, waits 30 seconds, then requests the declared board reset. [Three protected captures](../hardware/lab/observations/qotom-protected-normal-20260909/README.md) each recorded about 34.3 seconds of quiet. |
| Preserve halt mode and scenario semantics | The canonical kernel source is unchanged. Lab records identify the separate completion mode; an incorrect/missing terminal remains failure even if FreeBSD returns. |
| Independently recover a hung loader | The [loader-stall trial](../hardware/lab/observations/qotom-dated-watchdog-20260909/README.md) recorded one arm and recovery after 128.8 seconds, before its 300-second software escape. |
| Independently recover an early kernel hang | The [kernel-stall trial](../hardware/lab/observations/qotom-kernel-watchdog-20260909/README.md) recorded the pre-BOOT cli/hlt marker, 127.2 seconds of quiet, consumed request and authenticated FreeBSD recovery. |
| Capture before reboot, separate recovery bytes, check boot identity | The [runner](../scripts/run-qotom-recovery-lab.py) starts capture before SSH reboot, bounds bytes/time/cycle count, validates exact trace and quiet boundaries, checks a changed boot epoch and authenticated SSH, and reads consumed state. It saves recovery metadata before classifying raw bytes. |
| Three consecutive automated cycles | All three protected cycles passed directly through the runner, without parser correction, BIOS changes or operator reset. Per-cycle raw bytes, timed events, readback and results are retained. |
| Unarmed reboot and failed/interrupted arm | Actual post-reset boots defaulted to FreeBSD. The [historical physical rejection](../hardware/lab/observations/qotom-arm-rejected-20260909/README.md) returned safely without arming; its producer limitation is explicit. Current invalid-state and rejected-arm paths are exercised in GRUB/QEMU. |
| Unexpected terminal output | Classifier negatives reject changed/truncated traces, false success, duplicate records, missing protection and wrong digest. A returned OS cannot override a scenario failure. |
| Documented and tested rollback/disarm | [Rollback instructions](qotom-boot-recovery-lab.md#hang-recovery-and-rollback) retain USB identity/hash checks and manual bypass. A [physical configuration rollback](../hardware/lab/observations/qotom-recovery-restored-20260909/README.md) was read back and followed by a successful completed-run cycle. Every new cycle independently verifies disarmed state. |

The two watchdog-reset trials consumed their requests durably; neither needed
the RTC expiry fallback after reset. An unarmed physical probe established UTC
and advancing minutes, while QEMU replays prove stale-token rejection. The older
unbounded trial's repeated state remains unexplained and that request stays
disabled. The mechanism assumes the RTC advances and the reviewed board/register
contract remains valid. Future platform or device-policy changes require renewed
watchdog evidence. No claim covers power loss, arbitrary firmware failures or
later platform configurations that have not been exercised.

Validation: 28 GRUB/QEMU cases, protected-capture negative fixtures, retained
physical replay, and three protected hardware cycles. Emulator timer mocks are
labelled and are not used as proof that physical timer registers work.
