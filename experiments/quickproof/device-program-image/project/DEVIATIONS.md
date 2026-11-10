# Deviations of the device-program-image project

The theorem is about the program below, not about the kernel image byte for
byte. Every difference from the C the kernel compiles is listed here; quote a
result together with this file (QuickProof `docs/GUARANTEES.md`).

## D1. A wrapper unit (`patch/device_program_unit.c`)

The functions of `hardware/wifi/wifi-exec.h` are `static`. The unit includes
the header unchanged and gives each entry point an external name:

- `wifi_image_header`, which the kernel's three bind paths and the Qotom lab
  call alone, as `dp_header`;
- `wifi_start`, which they call next, as `dp_start`;
- `wifi_policy_within`, which the lab's `lab_dev_policy_admitted` calls, as
  `dp_within`;
- `wifi_service_admitted` and `wifi_source_admitted`, which the kernel's
  `device_service_admitted`, `network_source_admitted` and
  `dhcp_source_admitted` call, as `dp_service` and `dp_source`.

Each wrapper only forwards its arguments, and its body is proved like every
other function. The executor scratch `wifi_scratch` is a `static` array of
the header too; a sixth function, `dp_scratch`, returns its address, so that
the law can fill it before `wifi_start` and read it after.

## D2. `volatile` is defined away (`-Dvolatile=`)

`wifi_start` zeroes the scratch through a `volatile uint8_t *`, because a
device may write the scratch by DMA. VST cannot reason about volatile
accesses, so `quickproof.conf` compiles the unit with `-Dvolatile=`. The
theorem is therefore about ordinary stores. That nothing else writes the
scratch while `wifi_start` runs (no device is bound yet, and the kernel is
single-threaded) is the caller's obligation, outside the theorem.

## Not deviations, but limits of the law

- The policies an admission compares have at most `WIFI_MAX_SINKS` (8) sinks
  and `WIFI_MAX_DESCS` (16) descriptors. The parser guarantees this of a
  policy it accepts (the law proves it), and each kernel profile is a
  constant with fewer; a larger count would read past the arrays, and the law
  does not draw one.
- The image is an object of exactly its length, and the target, policy,
  header length and executor state are separate objects. The kernel passes
  its static program array and `sizeof` of it, and static objects.
- What a policy permits is the Lean model's (`LeanOS.DeviceProgramConfinement`
  and the executor's `ExecRefinement`); that each kernel profile is the Lean
  policy its comment names (`q35XhciPolicy`, `q35AhciPolicy`,
  `q35FrameSourcePolicy`, the Qotom policies) is checked by reading, not by
  this theorem.
- Single-threaded: nothing else writes the image, the policy or the scratch
  while a function runs.
- Partial correctness: termination is not claimed, though every loop is
  bounded.
