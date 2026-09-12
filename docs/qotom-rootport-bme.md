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
