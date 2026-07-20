# Direct port I/O authority model

`LeanOS.DirectPortIO` is a bounded Phase 2 policy for direct x86 port I/O. It
models the privilege-control fields relevant to the selected deny-all user
configuration and a finite authority manifest for the serial console, legacy
PIC, PIT, and `isa-debug-exit` devices.

The accepted control snapshot has IOPL zero, TSS descriptor limit 103, I/O-map
base 104, and no bitmap present within the descriptor. It also records that the
kernel produced the configuration and that a separate read-back matched. This
is the packed 104-byte TSS layout used by the selected target: the base is the
first byte beyond the descriptor limit. It grants no modeled user port.
`currentCpl` explicitly maps user origin to CPL3 and kernel origin to CPL0;
`selected_controls_deny_user_cpl` proves the finite privilege view denies CPL3,
while the separate manifest constrains the otherwise privileged CPL0 path.

## Authority and transition

Untrusted `PortOperation` values contain only a port, direction, width, and
value. They contain no origin or kernel purpose. `executeUser` therefore cannot
be redirected into a kernel operation: with accepted, freshly matched controls
it returns the typed modeled `#GP(0)` denial, and every path preserves the
identical complete `DeviceState` projection.

Trusted kernel dispatch adds one `Purpose`. `executeKernel` accepts only when
the live controls authorize kernel privilege and an exact `AuthorityKey`
appears in this manifest:

| Purpose | Port(s) | Direction | Width |
| --- | --- | --- | --- |
| Serial | `0x3f8`–`0x3fc` | Output | Byte |
| Serial status | `0x3fd` | Input | Byte |
| PIC | `0x20`, `0x21`, `0xa0`, `0xa1` | Output | Byte |
| PIT | `0x40`, `0x43` | Output | Byte |
| Debug exit | `0xf4` | Output | Byte |

The serial range in the table is only shorthand for five separately listed
keys; the model performs no range-based widening. A wrong purpose, port,
direction, or width rejects atomically. An accepted input observes without
mutation. An accepted output changes only the device class selected by its
trusted purpose.

`user_request_preserves_device_state` covers every user request, including
malformed stored policy and stale live read-back paths.
`kernel_acceptance_confined` exposes the live kernel-privilege authorization,
exact manifest membership, accepted stored controls, fresh live-control
equality, unchanged control state, and the precise device projection produced
by the accepted request.
`kernel_rejection_preserves_device_state` proves complete device-state equality
for every typed kernel rejection. The stable contract restates the user-denial
and kernel-confinement results, and `policy_nonvacuous` exhibits both a serial
output that changes the serial projection and a user denial of the same
port/value words with identical state.

## Scope and trusted boundary

This independently reviewable slice is the finite policy foundation for GitHub
issue #129. It does not modify issue #104's composite runtime, normalize vector 13,
add a generated codec, inspect the final ELF, or claim QEMU evidence. PCI
configuration ports and MMIO are outside this manifest; PCI DMA quarantine is
modeled separately and its later machine-inventory integration must assign its
configuration accesses a distinct reviewed authority rather than widening this
policy silently.

The proofs begin after a trusted adapter supplies the complete stored and live
control snapshots. TSS construction and loading, RFLAGS decoding, I/O-bitmap
and privilege-check semantics, exception delivery, instruction execution,
device behavior, handwritten C and assembly, generated code, compiler/linker
output, QEMU, physical hardware, and final-binary refinement remain unproved.
