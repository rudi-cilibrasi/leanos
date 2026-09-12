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
binding and serialize immutable inputs. Native emission, protected decoding and
physical capture remain to be implemented. This helper authorizes no write.
