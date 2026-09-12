# Qotom TXE firmware status observation

TXE remains an unresolved part of #330. The native header identifies 00:1a.0
as 8086:0f18, revision 0e, class 108000, type 0, Command 0106. A read-only
firmware-status sample will inform the next device contract. It cannot establish
that TXE DMA is disabled, transactions have drained or firmware is excluded.

The Intel-authored Linux v6.12 MEI driver binds device 0f18 to Bay Trail in
[pci-txe.c](https://github.com/torvalds/linux/blob/v6.12/drivers/misc/mei/pci-txe.c).
Its [register definitions](https://github.com/torvalds/linux/blob/v6.12/drivers/misc/mei/hw-txe-regs.h)
place firmware status DWORDs at PCI configuration offsets 40h and 48h.
[mei_txe_fw_status](https://github.com/torvalds/linux/blob/v6.12/drivers/misc/mei/hw-txe.c)
reads those two registers with pci_read_config_dword. Its aliveness and readiness
operations concern host communication and power gating; the inspected routines
do not provide a host-observable whole-engine DMA-drain guarantee. This last
statement is the scope of the inspected source, not proof that no such mechanism
exists elsewhere.

The helper performs ten configuration reads: identity, Command, class/revision
and header type; the two firmware status DWORDs; then the same four binding
reads. It requires the exact native identity and low Command word 0106, while
ignoring unrelated PCI Status and cache/latency fields. No BAR is dereferenced.
Successful output preserves both raw status DWORDs without interpreting a bit
pattern as readiness or authorization. All-ones status, read failure or changed
binding rejects with zero output. Statuses distinguish argument, initial header,
configuration read, binding drift, status read and absent status failures.

Tests enforce exact BDF/offset/order and the ten-read bound, every read failure,
every bound identity/Command/layout bit before and after sampling, unbound
Status/cache bits, all status payload bits, zero and all-ones samples, and
missing inputs. The caller still must establish native ECAM/root/firmware
binding and serialize immutable inputs. This helper authorizes no write.

## Native capture integration

The opt-in `--txe-status` build requires `--hda-bme`. After the preceding
HDA sequence returns successfully with its windows disarmed, the native stage
uses header index 4 and the existing firmware/root-bound ECAM reader. It clears
read authority before emitting `TXE-STATUS`; helper failures and local count
rejection (status 7) terminate with `qotom-txe-status`. Native tests check exact
output, all ten failed reads, wrong header and count, and disarm on every exit.

The protected runner fingerprints the decoder and retains `txe-status.json`.
The decoder requires the successful preceding HDA BME result, exact framing,
raw DWORD bounds, zero failed payloads and a matching terminal. Helper outcomes
other than initial-header rejection require the captured native TXE binding.
The actual TXE terminal is restored after earlier diagnostic projections.
Physical capture and build validation remain pending.
