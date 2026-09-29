# Device-program confinement

The Lean device programs (the BCM43224 WiFi driver, `docs/wifi-driver.md`,
the xHCI keyboard driver, `docs/usb-keyboard.md`, the AHCI identify
program, `docs/storage-ahci.md`, and the RTL8168 Ethernet program,
`docs/net-rtl8168.md`) run in ring 0 of the
lab kernel through the executor `hardware/wifi/wifi-exec.h`. Each program is
confined to a **policy** (`Policy` in `LeanOS/Wifi/Bytecode.lean`):

* the MMIO window (bytes of BAR0 it may address);
* the configuration dwords below 0x100 it may read, and those it may write;
* the command-register bits it may clear or set, changed only through the
  executor's read-modify-write `cfgUpdate32` whose masks are immediates;
* whether it may learn bus addresses of its scratch RAM (`physAddr`, DMA);
* its *address sinks*: MMIO address registers that may only receive bus
  addresses inside scratch (low dword) or zero (high dword).

| Device | Window | Config reads | Config writes | Command | DMA | Address sinks |
| --- | --- | --- | --- | --- | --- | --- |
| BCM43224 02:00.0 | 16 KiB | 0x00, 0x04 | 0x80, 0xAC (backplane windows) | may set Memory Space and clear Bus Master | no | — |
| xHCI 00:14.0 | 64 KiB | 0x00, 0x04, 0xD4, 0xDC | 0xD0, 0xD8 (port routing) | may set Memory Space and Bus Master | yes | CRCR, DCBAAP, ERSTBA, ERDP |
| AHCI 00:13.0 (ABAR) | 2 KiB | 0x00, 0x04 | — | may set Memory Space and Bus Master, clear Bus Master | yes | P1CLB, P1FB |
| RTL8168E-VL 01:00.0 (BAR2) | 4 KiB | 0x00, 0x04 | — | may set Memory Space and Bus Master, clear Bus Master | yes | DTCCR, TNPDS, THPDS, RDSAR |

## Three layers

1. **Static check.** `leanos-wifi-gen` emits an image only if
   `DeviceProgramConfinement.admissible` accepts the encoded program under the
   target's admitted policy. `run_confined` proves that such a program, run by
   the reference simulator `LeanOS/Wifi/Sim.lean` on any device model from any
   registers and scratch, never requests an effect outside the policy.
   `Policy.sane` (no direct header writes, no I/O Space, Bus Master only with
   DMA) holds for both Qotom policies.
2. **Declared policy.** The image (version 3) carries the policy. The
   simulator and the C executor both enforce it on every configuration access,
   command update and `physAddr` (status `policy` / `WIFI_POLICY`);
   `run_declared_confined` proves this alone confines any program.
3. **Admitted profile.** The lab kernel runs only version-3 images whose
   declared policy is no wider than its `lab_dev_profiles` entry for the target
   function (`hardware/lab/qotom-wifi.c.inc`); `qotom*Policy_bits` pins the
   Lean policies to that table.

Negative fixtures (`LeanOS/NegativeFixtures/DeviceProgramConfinement.lean`)
show that writing the command register or a BAR directly, setting Bus Master
under the WiFi policy, `physAddr` without DMA, out-of-window MMIO,
configuration offsets ≥ 0x100 (which alias under mechanism-1 access) and an
oversized target window are all rejected. `scripts/check-device-programs.sh`
generates the firmware-free programs through the check and cross-checks the C
executor against the simulator, on a fixed program and on seeded random
programs.

Hardware: `hardware/lab/observations/qotom-device-confinement-20260929`.

## Not covered

* That `wifi-exec.h` refines `Sim.step` is tested, not proved: differential
  fuzzing with a mutation self-test
  ([ADR 0020](adr/0020-device-program-executor-assurance.md)).
* Where a DMA-capable device writes beyond the root registers: pointers in
  scratch descriptors are a trusted assumption on the IOMMU-less J1900
  ([ADR 0021](adr/0021-j1900-device-dma-destinations.md)).
* What an allowed register write does inside the device, e.g. the BCM43224
  backplane windows reach every core on the chip.
* The programs still run in ring 0 of the lab kernel, not as kernel subjects
  (#449).
