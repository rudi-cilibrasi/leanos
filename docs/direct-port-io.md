# Direct port I/O authority model

`LeanOS.DirectPortIO` is a bounded Phase 2 policy for direct x86 port I/O. It
models the privilege-control fields relevant to the selected deny-all user
configuration and a finite authority manifest for the serial console, legacy
PIC, PIT, and `isa-debug-exit` devices.

The accepted control snapshot has IOPL zero, TSS descriptor limit 103 with
descriptor granularity `G=0`, I/O-map base 104, and no bitmap present within
the descriptor. It also records that the kernel produced the configuration and
that a separate read-back matched. This is the packed 104-byte TSS layout used
by the selected target: with byte granularity, the base is the first byte
beyond the effective descriptor limit. A page-granular descriptor is rejected
even when its raw 20-bit limit is 103, because scaling that limit would expose
the following bytes as a live I/O bitmap. The accepted snapshot grants no
modeled user port.
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
trusted purpose. Before that output becomes device-visible, `Width.normalize`
discards every request bit above the authorized byte, word, or double-word
width, matching the value consumed by the corresponding x86 output operation.

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
`byte_output_discards_upper_bits` is the concrete `outb` regression: accepted
byte requests with values `0x100` and `0` produce identical transitions and a
device-visible serial value of zero.

## Scope and trusted boundary

Every bootable ELF in the emulator evidence matrix is checked by
`scripts/check-direct-port-sites.py` against an exact variant-specific manifest.
The inventory binds every `in`, `out`, `ins*`, and `outs*` instruction to a named
wrapper/site and reviewed owner. The C wrappers are deliberately not inlined so
compiler duplication cannot turn one reviewed primitive into ambient,
untracked authority. A separate source-operation manifest binds every shared
byte-wrapper invocation to its caller, exact constant port, and matching
serial, PIC, PIT, or debug-exit purpose. Semantic negative fixtures prove that
an omitted opcode/site, a conditional-only opcode, an unauthorized `out8`
caller, a misclassified PCI wrapper, and runtime-handler reuse of a PCI helper
make the policy fail.

PCI configuration ports and MMIO remain outside the ordinary direct-port
manifest. The three width-specific wrappers used only with configuration
mechanism #1 ports `0xcf8` and `0xcfc` are classified separately as
`DMAQuarantine.boot-pci-config`, a boot-only exception owned by the DMA
quarantine checkpoint rather than a widening of ordinary kernel direct-port
authority. The optimized final-ELF call graph must bind those wrappers to the
two PCI helpers, the helpers to `quarantine_q35_pci_dma`, and that checkpoint to
`kernel_main`. An instruction-level control-flow graph additionally requires
the quarantine call to be reachable from `kernel_main` entry and to dominate
its sole call to `enter_user`; a skipped-quarantine fixture jumps over the
earlier call and is rejected.

The proofs begin after a trusted adapter supplies the complete stored and live
control snapshots. TSS construction and loading, RFLAGS decoding, I/O-bitmap
and privilege-check semantics, exception delivery, instruction execution,
device behavior, handwritten C and assembly, generated code, compiler/linker
output, QEMU, physical hardware, and final-binary refinement remain unproved.

The executable CPL3 denial crosses the shared vector-13 entry normalizer and
the existing atomic fault-cleanup/survivor-dispatch adapter. It retires the
faulting subject, restores the scheduler-selected peer's kernel-owned saved
context under that peer's address space, and reaches the peer only through the
validated user-return epilogue; the denied `OUT` instruction is never skipped
or resumed. Dedicated negative images mutate the I/O-map base, raw descriptor
limit, and descriptor granularity independently and must all fail at the live
control read-back before CPL3 entry.
