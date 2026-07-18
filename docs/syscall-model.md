# Caller-confined syscall model

`LeanOS.Syscall` defines a total Phase 2 abstract syscall boundary. Trusted
kernel context supplies the caller subject and active address space. An
untrusted call supplies exactly four `UInt64` words: a syscall number and three
arguments. No argument position denotes a subject or address space, so changing
any attacker-controlled word cannot impersonate another subject or select a
different address space.

The initial scalar vocabulary is intentionally small:

| Number | Operation | Arguments |
| --- | --- | --- |
| `0` | map | capability handle, virtual page, permission bits (`1` read, `2` write, `3` both) |
| `1` | unmap | virtual page, followed by two zero words |
| `2` | access check | virtual page, access (`0` read or `1` write), then zero |

All other numbers, permission bitsets, access values, and nonzero reserved
arguments produce typed decoding errors. The map capability argument uses the
canonical 16-bit-slot/48-bit-generation encoding from
`LeanOS.CapabilityHandle`. Before `VirtualMapping.map` receives the decoded
slot, `CapabilityHandle.resolveCurrent` checks that the complete opaque
`UInt64` names the exact live memory capability in the trusted caller's
capability space. Reserved encodings, wrong generations, wrong kinds, retired
objects, and capabilities belonging to another trusted caller produce typed
handle denials without changing state. Scalar conversion is total. The
dispatcher does not reimplement ownership, lifetime, or allocator policy.
Access-check success returns no frame or kernel object identifier, so a return
value does not itself become authority. New calls must be added explicitly:
there is no default privileged operation.

Machine-checked theorems prove deterministic, unambiguous decoding; preservation
of the complete lifecycle/mapping invariant for every dispatch; complete-state
preservation on every rejection; unchanged capability state and therefore
pre-state provenance for every subject's post-state authority; and complete
state preservation when a caller tries to operate in another owner's active
address space. Executable adversarial traces cover forged context via argument
words, unknown syscall numbers, malformed permissions, malformed and stale
generation-bound map handles, cross-address-space map and unmap attempts, a
valid map/access path, and replay after address-space destruction.

The allocation-free `syscallDemo` export keeps one fixed accepted witness for
this contract, now using the canonical generation-bound map word. A
machine-checked agreement theorem connects that witness to the migrated
dispatcher, and hosted and QEMU oracle replay check the generated scalar
adapter. This remains integration evidence, not proof of compiler, runtime, or
binary refinement.

The trusted-context values are assumptions of this model. A future entry path
must derive them from protected kernel execution state; this model does not
prove that assembly or hardware does so. Address-space create/destroy remain
internal lifecycle operations in this first vocabulary. Raw pointers, memory
copying, register layout, x86-64 entry/return, scheduling, IPC, concurrency,
blocking, generated code, the boot image, and ABI stability are out of scope.
The Lean proofs describe only this sequential abstract state machine; build or
QEMU success is integration evidence, not refinement of a kernel binary.

This slice adds no axiom, proof escape, FFI, unsafe declaration, or new trusted
code. Its sole new trust assumption is the explicitly modeled provenance of
`TrustedContext`.
