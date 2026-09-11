# Qotom native ECAM capture — 2026-09-11

The opt-in image armed after exact captured firmware equality and active-root/
control checks. Native ECAM enumeration completed with status0 and 16 functions,
with no reported transaction fault. All BDF/vendor/device/class identities match
the earlier completed mechanism-1 capture. EHCI00:1d.0 (8086:0f34, class0c0320)
is present through this separate access path. The fifteen-function generated
inventory policy returns65536, so FINAL remains qotom-platform-pending.
No DMA quarantine, platform admission or CPL3 execution is claimed.

Installed ELF SHA256
1c2f901a22280ae8b4a63471f94c63ae7e8afbc98109aae01930a656d85f70ac.
The build manifest records its actual dirty build-time source and every input
hash; subsequent source commits do not rewrite that provenance. USB boot files
were backed up to /var/tmp/leanos-before-ecam-05ce325.tar.gz. Installation used
direct copies, fsck and read-only hash verification. Internal disk unchanged.

The physical runner initially rejected this capture after FreeBSD recovery:
its firmware comparator incorrectly included the historical handoff_sha256.
The loader handoff hash changed with the rebuilt ELF; every firmware table,
physical address and byte matched the reviewed snapshot. The comparator now
excludes only handoff_sha256, whose binding to the actual handoff remains checked
by the preceding ACPI decoder. The saved bytes were reclassified without another
reboot. initial-runner.log and original diagnostic-replay-inputs.json retain the
failure and original decoder inputs; cycle-1/reclassified-result.json records
the corrected replay and its updated input hashes. No original successful runner
exit is claimed.

Post-terminal quiet34.32546106498921s. FreeBSD boot time1789132116→1789135898;
SSH restored, request consumed and grubenv requestnone independently verified.
Raw serial/events, native handoff and all twelve ACPI tables are retained.
This confirms the bounded ECAM read path on this boot, not general resource
ownership or firmware/AP exclusion. Read-only Command exceptions, TXE/DMA drain,
USB ownership and the full hardware admission profile remain unresolved.
