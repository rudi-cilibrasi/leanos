# Qotom Broadcom D3hot transition

The Qotom inventory contains a Broadcom BCM43224 endpoint at `02:00.0`
(`14e4:4353`, subsystem `14e4:04d8`). It is reached through root port
`00:1c.1`. FreeBSD identifies the device as `bwn_pci0`; its driver shutdown
path stops firmware, DMA rings, the chip and PHY before suspending the bhnd
core. LeanOS cannot reuse that driver path, so this stage makes a smaller,
explicit PCI power transition and retains its exact limits.

The arm gate binds the copied Qotom firmware tables and active ECAM root to the
exact endpoint, its bus-2 bridge route, the retained four-entry capability
list, PCIe Device Capability/Status words, and successful bridge BME and
Transactions Pending priors. It then grants a two-store window. The first and
only accepted store at stage zero writes Command `0000`, disabling I/O-space,
memory-space and bus-master enable. A successful store, restored temporary
mapping and unchanged control registers grants the second store at PMCSR.
Every rejected request or reported store failure consumes the grant; mapping
or control interference is terminal.

The bridge prior accepts Device Status `0010` or `0011`. Bit zero is the sticky
Correctable Error Detected report and varied across consecutive physical
boots; it grants no authority. Every other bit must match `0010`, including a
clear Transactions Pending bit.

The transition refreshes the endpoint header, complete capability list, PCIe
payload and PM state before the first write. It verifies Command readback,
refreshes the same state with Command zero, and obtains two Transactions
Pending-clear samples separated by the bounded 10 ms ACPI PM-timer delay. It
then requires PMCSR `4008`: D0, PME disabled, and the retained device-specific
bits. The second store writes `400b`, changing only the power-state field to
D3hot. The final checks require configuration access, Command zero, PMCSR
`400b`, and the unchanged four-entry capability list.

PCI Power Management 1.2 requires compliant functions to support D0, D3hot and
D3cold. In D3hot the function remains configuration accessible while normal
I/O-space and memory-space responses and functional interrupts are disabled;
PME is its defined action. The same specification requires software to disable
I/O, memory and bus mastering and ensure host-initiated transactions are no
longer pending before entering D3. This bounded sequence checks those visible
preconditions for this endpoint and leaves PME disabled.

Status 0 means the full sequence and final checks succeeded. Statuses 1–11
cover arguments, typed priors, the initial refresh, Command read/write/readback,
Transactions Pending, the final D0 refresh, PMCSR write/readback and final
configuration checks. Native statuses 12 and 13 cover snapshot/prerequisite and
arm or timer rejection. The decoder accepts only the exact success record with
the existing `qotom-platform-pending` terminal, or a reachable failure record
with `qotom-broadcom-d3`. It projects the stream back through the prior PCIe
pending decoder and fingerprints both decoders.

This sequence does not execute the FreeBSD device shutdown path and does not
show that Broadcom firmware or its internal engines were stopped. It does not
establish completion of posted writes, continuing firmware or AP exclusion,
whole-machine DMA quarantine, or a D3cold transition. A failed store may have
taken effect; the lab deliberately does not restore D0. The native terminal
therefore remains `qotom-platform-pending`.

`tests/pci-power-observation.c` checks PM capability discovery, bracketed PMCSR
reads, list drift, field bounds and every read failure. The Broadcom core,
two-store window and arm tests cover exact successful ordering, all read and
write failures, delayed pending checks, stale identities and priors, aliases,
rearm rejection, and terminal interference. Decoder and protected-runner tests
cover success, every reachable failure, scalar and framing rejection, terminal
contradictions, prior-stream projection, and decoder hashing.

Build the opt-in image with `--broadcom-d3` after the complete
`--pcie-pending` dependency chain. The builder selects
`build/qotom-broadcom-d3-lab`; the runner uses the matching `--broadcom-d3`
flag and writes `broadcom-d3.json`.
