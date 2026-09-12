# Qotom Valleyview graphics-ring observation

This opt-in Qotom lab stage observes the integrated graphics function at
`00:02.0` after the existing Broadcom D3hot stage. It preserves the boot-time
PCI Command `0007`, BAR0 memory decode, BAR2 framebuffer decode and graphics bus
mastering. FreeBSD later reports `0407` because it also sets Interrupt Disable;
the protected LeanOS boot captures `0007` before FreeBSD changes that bit.
That choice keeps the firmware-established display path available while #335
is being tested and grants no device-control write.

The endpoint gate binds the retained `8086:0f31`, class `030000`, revision 0e
header and its exact Qotom BAR layout:

- BAR0 `d0000000`, 4 MiB graphics MMIO
- BAR2 `c0000000`, 256 MiB prefetchable aperture
- BAR4 `f080`, 8-byte I/O aperture

The observer samples the three Valleyview engines exposed by Linux's pinned
i915 device description: RCS, VCS and BCS. The pinned register definitions put
their ring bases at `0x2000`, `0x12000` and `0x22000`; each sample reads TAIL
`+0x30`, HEAD `+0x34`, START `+0x38`, CTL `+0x3c` and MI_MODE `+0x9c`.
The [Valleyview engine mask](https://github.com/torvalds/linux/blob/cba2348ab114391f5b1a00fa65c5b739f13f0563/drivers/gpu/drm/i915/i915_pci.c),
[engine bases](https://github.com/torvalds/linux/blob/cba2348ab114391f5b1a00fa65c5b739f13f0563/drivers/gpu/drm/i915/i915_reg.h),
and [ring register offsets](https://github.com/torvalds/linux/blob/cba2348ab114391f5b1a00fa65c5b739f13f0563/drivers/gpu/drm/i915/gt/intel_engine_regs.h)
are pinned to Linux commit `cba2348ab114391f5b1a00fa65c5b739f13f0563`.

Sixteen complete PCI-header reads precede the MMIO transaction. Two ordered
fifteen-register samples follow, then sixteen more header reads reject identity,
BAR or Command drift. Successful output therefore represents exactly 62 reads.
The serial record retains all 30 raw dwords. Its decoder reports whether both
samples are identical, whether every ring has CTL.Valid clear and MI_MODE.Idle
set, and whether every sampled head equals its tail. Those derived values are
observations, not authority to clear BME.

The MMIO window maps one of the three approved physical register pages at a
time into the existing private low aperture as supervisor read-only, NX and
PAT-slot-3 UC. Arming binds the copied firmware tables and active CR3 hierarchy,
and rejects any existing mapping of any page in the complete BAR0 or BAR2
resource. Every access restores the aperture and rechecks controls; mapping or
root interference is terminal.

The stage does not establish display ownership, ring shutdown, interrupt
quiescence, DMA drain, posted-write completion, or continuing firmware/AP
exclusion. It leaves graphics BME set and the native terminal at
`qotom-platform-pending`. Physical LeanOS evidence will be retained after the
first protected run.

Build the complete opt-in image by adding `--graphics-state` after the existing
`--broadcom-d3` dependency chain. The builder writes
`build/qotom-graphics-state-lab/leanos-qotom-lab.elf`; the runner's matching
`--graphics-state` option validates and writes `graphics-state.json`.
