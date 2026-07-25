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

The executable CPL3 denial crosses the shared generated vector-13 manifest
normalizer with its user-only hardware-error shape and typed
general-protection purpose. The handler then binds `#GP(0)`, the reviewed
instruction address, and the saved `DX`/`AL` operands before reaching
the existing atomic fault-cleanup/survivor-dispatch adapter. It retires the
faulting subject, restores the scheduler-selected peer's kernel-owned saved
context under that peer's address space, and reaches the peer only through the
validated user-return epilogue; the denied `OUT` instruction is never skipped
or resumed. Dedicated negative images mutate the I/O-map base, raw descriptor
limit, and descriptor granularity independently and must all fail at the live
control read-back before CPL3 entry.

Four booted probes exercise this path as mandatory accepted-boot rows in the
emulator matrix, each executing exactly one reviewed raw CPL3 instruction: a
byte `OUT` to serial data `0x3f8`, a byte `OUT` to `isa-debug-exit` `0xf4` with
a distinctive guest-error value, a non-destructive byte `IN` from serial
line-status `0x3fd`, and a byte `OUT` of `0x00` to the master PIC data/mask
register `0x21`. The PIC probe carries an independent hardware failure oracle
that does not trust the serial transcript: `privilege_init` masks every legacy
IRQ line (`out8(0x21, 0xff)`), and after the denial the surviving peer's
kernel-visible operation performs the inventoried CPL0 read-back `in8(0x21)` and
requires the observed mask to still be `0xff`. If the attacker's write had
reached the device the mask would read `0x00` and the kernel fail-stops with
`direct-port-pic-canary`, even under a forged `device-mutation=0` transcript.
The read-back is bound in `scripts/direct-port-byte-operations.tsv` as a
`DirectPortIO.pic` byte operation, and `scripts/test-run-direct-port-pic.sh`
drives controlled runner negatives for an actually-executed write, a mutated or
missing canary, forged and reordered records, an attacker-selected survivor, a
stale address space, guest error, reset, triple fault, and timeout.

## Composed port-denial containment

`LeanOS.DirectPortContainment` is the first model-level composition slice
between this port-authority policy and the atomic user-fault
cleanup/survivor-dispatch transition of `LeanOS.FaultDispatch`. Its
`containDeniedPort` step sequences the two existing model boundaries in the
order the booted machine exercises them: the untrusted `PortOperation` is first
denied by `DirectPortIO.executeUser`, and the same normalized user-fault entry
then drives `FaultDispatch.dispatch` to retire the kernel-selected current
subject and select the next survivor context. It introduces no second
authorization table, fault scheduler, or vector-13 classifier; the machine
binds the `#GP(0)` through the shared generated vector-13 normalizer and reuses
the vector-14 user-fault containment dispatch for cleanup, exactly as this
composition sequences the two models.

`denied_port_contained` proves, under exact accepted deny-all controls with a
freshly matched live read-back and any successful atomic cleanup/dispatch, that
the port attempt returns the modeled `#GP(0)`, the complete device projection is
unchanged, the finite privilege view denies CPL3, and the authoritative current
subject is retired: it becomes dead and non-runnable, leaves the ready queue and
current slot, loses its resumable context, and loses every address space and
mapping it owned. `untrusted_words_cannot_select` proves that neither untrusted
port operation reaches a kernel acceptance and that the survivor selection is
independent of the untrusted port/value/width words, while
`attacker_registers_cannot_relabel` records that the attacker register bank is
not an input to the composed transition.
`denied_attempt_cannot_return_to_faulting` isolates the no-return-to-A
conclusion. `denied_port_contained_nonvacuous`,
`witness_serial_denied_and_dispatched`, and `witness_untrusted_probe_independent`
supply a concrete two-subject witness in which subject A's serial-console,
`isa-debug-exit`, and PIC-control probes are all denied with the identical
device projection and identical survivor dispatch of subject B, and the negative
fixture `tests/negative/DirectPortContainmentExposedControls.lean` shows the
accepted-controls hypothesis is load-bearing. The stable contract restates the
composed result as `SC-DIRECT-PORT-CONTAINMENT`. As with the underlying models,
x86 privilege/exception delivery, the normalized-entry-to-model refinement, the
generated adapters, machine cleanup/CR3 writes, QEMU, and the final binary
remain trusted boundaries rather than theorem claims.
