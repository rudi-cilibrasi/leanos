# Bounded conventional PCI capability observation

`boot/pci-capabilities.h` follows a function's conventional capability list
through the existing read-only configuration callback. Type-0 and type-1
headers use Status bit 4 and the byte pointer at offset 0x34. Every capability
header is retained as its raw dword and offset. There is no capability-payload
interpretation, extended-capability traversal, device write or DMA admission.

The conventional header locations and capability IDs are also defined in the
[Linux PCI register declarations](https://github.com/torvalds/linux/blob/master/include/uapi/linux/pci_regs.h).
This collector deliberately rejects nonzero reserved alignment bits rather
than silently masking them. Each followed pointer must be an aligned slot in
0x40–0xfc. A 48-bit visited set prevents cycles, including self-links. Acyclic
backward links remain valid. At most four initial checks and 48 capability
reads occur, with fixed storage and no allocation.

Before traversal, the callback rechecks identity, the capability-list status
bit, the full header-type byte and the list-head byte against the supplied
immutable initial header. Other Command/Status bits may change and are not
certified by this check. Serialization, read fidelity and input/output
non-aliasing are caller obligations; the initial recheck cannot make later
hardware observations atomic. Failed reads, changed checked fields, absent
capability headers, malformed pointers and cycles publish count zero. Staged
array entries on failure must not be consumed.

The [FreeBSD survey](../hardware/lab/observations/qotom-freebsd-capabilities-20260911/pciconf-lc.txt)
records a read-only `pciconf -lc` run. It provides capability locations for
controller-policy investigation. For example, the Broadcom list follows
0x40, 0x58, 0x48, 0xd0; the backward-link test uses that ordering with synthetic
header contents. This is an OS-derived survey, not native LeanOS capability
bytes. FreeBSD's list also lacks the EHCI function present in the retained
native boot, so it cannot replace the native sixteen-function baseline.

`check-pci-capabilities.sh` checks maximum-length lists, every cycle/failure
position in that list, every invalid nonzero pointer, initial-header drift,
absent capabilities, no-list status and the backward-link example in ordinary
and pinned ASan/UBSan builds. Native ECAM collection and retained raw capability
records remain the next step. Quarantine control semantics, USB ownership,
TXE behavior and transaction drain remain unresolved under issue #330.
