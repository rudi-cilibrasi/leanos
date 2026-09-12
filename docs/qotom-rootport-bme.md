# Qotom root-port bus-master gating candidate

Four root ports at 00:1c.0–3 still report initial Command 0007. This candidate
clears only BME with a word write of 0003 while retaining memory and I/O decode.
The reviewed scope is the four native 8086:0f48/0f4a/0f4c/0f4e identities,
class/revision 0604000e and header byte 81. It does not stop downstream engines.

[Intel 329670-002 section 17.6.2](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf#page=708)
states that BME gates upstream memory and I/O requests. Completions and other
request classes are not gated. This is a request-forwarding control, not a
whole-fabric drain mechanism. No transaction-drain or DMA-admission conclusion
follows from this candidate.

The helper requires a successful PCIe observation at offset 40h, Device
Capabilities 8000, zero Device Control and clear Transactions Pending. The
other five Device Status bits may vary. It refreshes the full sixteen-DWORD
bridge header and complete PCIe capability/list observation, checks Command7,
attempts one word write, checks immediate Command3, repeats the complete
refresh and checks final Command3. Primary and secondary Status are excluded
from header equality except the capability-list indicator; all routing and
control fields remain bound to the initial snapshot. PCI Status is not written.

The bound is 247 configuration reads and one word write. The native four-entry
capability lists use 71 reads. Failed writes retain attempted/before/after
results and may have effects; there is no retry or rollback. Failure before the
write leaves zero output. No link control, endpoint register, reset or polling
operation is introduced. Clear Transactions Pending samples are not a proof
of no outstanding posted writes or future firmware activity.

The caller must bind the exact native inventory, ECAM mappings, firmware and
roots and provide immutable nonaliasing observations and serialized bounded
callbacks. Tests cover all four identities, exact read order, every read failure,
initial/final routing/control/payload bits, asynchronous Status fields, ignored
and ambiguous writes, pending transactions and BME reassertion. Consumed native
write authority, decoder/runner integration and physical validation remain
pending. This helper has not been installed or run on the Qotom.

## Consumed native write window

The writer is armed for exactly one function in 00:1c.0–3. It accepts only
that BDF, offset 4 and word 0003. Every request consumes authority, including
wrong-function and invalid-value requests. The temporary leaf is
`80000000e00e001b + function * 1000` (hexadecimal): RW/NX/supervisor UC.
The trusted primitive stores one word at aperture+4, then the exact prior leaf
is restored with invalidations and control checks. Interference is terminal.

Arming binds the native header, prior PCIe state, copied firmware, compiled
root views and ECAM alias exclusion. It publishes the selected function only
after checks pass. A rejected rearm clears all authority, including the old
function. Arming neither maps a device nor reads/writes its registers. The
helper still refreshes all routing and capability state before its write.

Tests cover the four mapped function pages, other-function rejection, every
alternative word value, missing callbacks, invalid apertures, failed stores,
mapping/restore interference, both control observations, rejected rearm,
identity/prior-state bit changes and all 4096 possible aliases of each target
ECAM page. The protected physical result is retained below.

## Native capture path

The opt-in `--rootport-bme` build requires `--txe-status`. Earlier PCIe capture
retains each observation only with an exact sixteen-function count. After
the TXE stage returns, the root-port stage uses headers/capability lists and
prior PCIe observations at indices 6–9. Each port is armed, executed and
disarmed before its record is emitted. A nonzero outcome halts immediately;
no later port is accessed. Local count/arm rejection is status 8.

The native test executes the actual arm, helper and window with modeled
configuration and store callbacks. It covers every one of the 71 failed reads
on each port, store failures, prior-state rejection and wrong count. It checks
exact ordered output and that no later port is accessed after failure.

The runner fingerprints the decoder and saves `rootport-bme.json`. The decoder
requires a successful preceding TXE observation, contiguous indices 6–9 and
all four successes or a prefix ending at the first failure. It rejects writes
after failure, forged initial Command/PCIe state, invalid result combinations
and terminal contradictions. Actual root-port termination is restored after
earlier projections. Native build and physical validation passed.

## Physical result

The [retained capture](../hardware/lab/observations/qotom-native-rootport-bme-20260911/README.md)
contains all four successful writes, indices 6–9, Command 0007 to 0003.
The expected terminal remains `qotom-platform-pending`. FreeBSD recovered
with a changed boot time and consumed request; independent SSH verified BIOS
boot and installed hashes. The retained replay checks complete timed serial
classification, exact records, terminal, quiet interval and recovery metadata.
These results establish the bounded transitions, not whole-platform admission.
