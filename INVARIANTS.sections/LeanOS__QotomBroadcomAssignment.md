# Assigned-Broadcom variant of the Qotom PCI trust contract

The variant `qotom-j1900-pci-trust-v1-bcm43224-assign-v1` lets the lab return the Broadcom WiFi device at `02:00.0` from its quarantine power state D3hot to D0 and hand it to the WiFi driver subject. It decides scalar observations supplied by the lab; it does not prove those observations are fresh or faithful, or that the device obeys them.

- `write_one_iff` — The store check returns one exactly when the initial trust contract accepted, the earlier D3hot record is the exact successful one, the device still reads Command zero, D3hot and its original BARs, and the store is the 16-bit power-control write of D0.
- `write_exact` — Whatever else is supplied, the only configuration store the variant ever permits is the 16-bit write of `4008` to the power-control register at offset `44`.
- `write_requires_contract` — The store is never permitted unless the initial trust contract accepted.
- `admission_one_iff` — Assignment is admitted exactly when the store was the permitted one, every check after the transition matches, and the offered program policy is assignable.
- `admission_post_state` — After an admitted assignment the device reads D0, Command zero, its original BARs and a clear Transactions Pending bit, confirmed by at least two quiet samples.
- `admission_requires_write` — An admitted assignment always rests on the permitted store and the accepted initial trust contract.
- `admission_policy_no_bus_master` — An admitted program targets exactly `02:00.0`, declares no DMA, can never set Bus Master, and cannot write the Command or power-control registers.
- `qotomBcm43224Policy_assignable` — The reviewed Broadcom device-program policy itself satisfies the assignment conditions.
