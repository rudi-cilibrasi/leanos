# Qotom PCIe non-posted quiet observation

The retained PCIe Device observations expose Device Status.Transactions
Pending on the four root ports at indices 6–9 and the two Realtek endpoints at
indices 13 and 15. This stage checks that bit after the successful root-port
and endpoint BME transitions. The Broadcom endpoint at index 14 is handled by
the subsequent [bounded Command-off and D3hot stage](qotom-broadcom-d3.md),
whose remaining ownership and shutdown limits are explicit.

The helper accepts the exact prior PCIe observation and a successful typed BME
result. Realtek inputs also require the retained stopped engine state. Every
poll checks Command `0003`, uses the existing PCIe observer to perform two
complete identity and capability-list collections around the Device Capability
and Device Control/Status reads, then checks Command `0003` again. All payload
bits except Transactions Pending must match the prior observation.

Success requires two clear Transactions Pending samples separated by a 10 ms
ACPI PM-timer delay. The bound is 100 observations and 99 delays. The first
read, identity, capability, payload, Command or timer failure stops the stage.
Statuses are 0 success, 1 argument, 2 invalid typed prior, 3 Command, 4 PCIe
observation, 5 changed payload, 6 delay and 7 timeout. Native statuses 8 and 9
cover local ECAM/prerequisite and PM-timer arm rejection before polling.

The PM timer is bound to the exact copied FADT and LPC identity, Command and
ACPI base. Each function receives a new ECAM reader and timer arm. Both are
revoked before serial output or terminal failure. The native path emits indices
6, 7, 8, 9, 13 and 15 in that order and stops after the first failure. The
strict decoder requires a successful preceding two-endpoint Realtek BME prefix,
the exact successful six-function sequence or a failure prefix, and the matching
terminal reason. It records that no hardware operation was replayed.

PCIe Transactions Pending describes outstanding non-posted requests from one
Function. Two clear samples establish a bounded non-posted quiet observation
for these six functions. They do not show that posted writes reached memory,
exclude later firmware, AP or device activity, cover the Broadcom endpoint in
this stage, or establish transaction drain or whole-machine DMA quarantine. The native
terminal therefore remains `qotom-platform-pending`.

`tests/qotom-pcie-pending.c` covers pending-to-clear, the 100-poll timeout,
timer failure, Command and payload drift, every first-observation read failure,
and typed root-port/Realtek prerequisites. The native lab test exercises all
six functions, separate arms, exact records, timer use, timeout, read failure,
prerequisite rejection and disarm. Decoder tests cover success, every reachable
failure status, ordering, scalar bounds, terminal contradictions and protected
recovery projection.

Build the opt-in image with `--pcie-pending` in addition to the complete
`--realtek-bme` dependency chain. The builder selects
`build/qotom-pcie-pending-lab`; the runner fingerprints the decoder and writes
`pcie-pending.json`.

## Physical result

The [protected Qotom capture](../hardware/lab/observations/qotom-native-pcie-pending-20260912/README.md)
reported status 0 and two samples for all six functions. Device Status was 17,
17, 17, 16, 25 and 25 for indices 6, 7, 8, 9, 13 and 15 respectively, with
Transactions Pending clear. The expected terminal remained
`qotom-platform-pending`. FreeBSD recovered with a changed boot time, and the
request was consumed. Independent replay and post-recovery USB verification
passed. These results retain the scope limitations above.
