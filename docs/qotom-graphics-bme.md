# Qotom graphics bus-master gating candidate

This opt-in stage follows the successful Valleyview ring observation and clears
only PCI Command Bus Master Enable on integrated graphics `00:02.0`. The
transition is `0007` to `0003`; memory and I/O decode remain enabled so the
firmware-established display apertures are not disabled by the PCI write.

The helper accepts only a successful retained observation in which RCS, VCS and
BCS have identical samples, every ring has equal head and tail, CTL.Valid is
clear and MI_MODE.Idle is set. It repeats the complete 62-read observation,
reads Command, attempts one exact 16-bit write, checks immediate Command
readback, repeats all 62 reads using a header bound to Command `0003`, and checks
Command once more. The complete bound is 127 reads and one word write.

The final observation must exactly equal the retained pre-write values. This
checks that the three sampled rings remain idle and empty around the BME
transition. It does not prove that display or graphics firmware owns no other
engine, that all posted writes completed, that no agent can re-enable BME, or
that all graphics memory transactions are quiescent. A failed write may have
effects and is reported; the helper does not retry or roll back.

## Consumed native authority

The writer accepts only BDF `00:02.0`, configuration offset 4, width 16 and
value `0003`. Every request consumes authority. It temporarily maps physical
ECAM page `e0010000` into the private aperture as RW, supervisor, NX and UC,
executes one trusted word store, restores the exact leaf, invalidates both
changes and rechecks active controls. Mapping, restoration or root interference
is terminal.

Arming binds the exact `8086:0f31` boot header, quiet retained ring state,
copied firmware tables, active CR3 hierarchy and absence of every ECAM alias.
The separately armed graphics reader retains its full BAR0/BAR2 alias
exclusion. Neither arm path accesses the device, and every rejected rearm first
revokes previous authority.

Tests cover the exact read and write order, every one of 127 read failures,
failed and ambiguous stores, BME reassertion, ring-state drift, all alternative
write values and BDF fields, mapping/restoration interference, missing
callbacks, every ECAM alias, header and retained-state mutations, and native
emission/disarm behavior. Ordinary and pinned ASan/UBSan executions run through
the device-control suite.

Build with `--graphics-bme` after the complete `--graphics-state` dependency
chain. The protected runner's matching option decodes `GRAPHICS-BME`, preserves
raw before/after Command values, and continues to classify success as
`qotom-platform-pending`.

The [retained Win7 Legacy capture](../hardware/lab/observations/qotom-native-graphics-bme-20260912)
completed the full stage on Qotom hardware. Both ring samples remained zeroed,
idle and empty around the single Command transition from `0007` to `0003`.
The capture also records the digest-bound image, raw serial stream, independent
decoder output, consumed request and automatic FreeBSD recovery. This is
physical evidence for the bounded transition; the ownership, exclusion, drain
and quarantine limits above remain open.
