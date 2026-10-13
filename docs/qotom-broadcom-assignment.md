# Qotom Broadcom assignment variant

The [initial trust contract](qotom-pci-final-admission.md)
`qotom-j1900-pci-trust-v1` leaves the Broadcom BCM43224 at `02:00.0` in D3hot
with Command `0000` ([D3hot stage](qotom-broadcom-d3.md)). The WiFi driver
subject of the [network-subject lab image](wifi-driver.md) needs the device in
D0. The reviewed variant `qotom-j1900-pci-trust-v1-bcm43224-assign-v1`
([ADR 0027](adr/0027-qotom-broadcom-assignment-contract.md)) states the one
configuration store that returns the device to D0, the checks after it, and
when the device may be assigned to the driver subject. It replaces the
lab-only step of issue #450.

## Hardware facts and sources

| Fact | Value | Source |
| --- | --- | --- |
| D3 record of this boot | Command `0006` to `0000`, PMCSR `4008` to `400b`, two quiet samples, Device Status `0019` | Every retained `BROADCOM-D3` capture, for example [`qotom-native-broadcom-d3-20260912`](../hardware/lab/observations/qotom-native-broadcom-d3-20260912/README.md) and the device-stream capture of 2026-10-07 |
| PM capability and PMCSR offset | capability at `40`, PMCSR at `44` | Retained capability list; PCI PM 1.2 places PMCSR at capability + 4 |
| PMCSR in D0 and D3hot | `4008` and `400b` | The same captures. Both keep PME disabled and No_Soft_Reset (bit 3) set. |
| BARs | BAR0 `d0700004` (64-bit memory), BAR1 `00000000` | Retained native inventory header of `02:00.0` |
| PCIe Device Capability, Control/Status | `05908fa0`, `00190000` | Retained PCIe observation of `02:00.0` in D0; Transactions Pending clear |
| Configuration context across D3hot to D0 | kept | PCI PM 1.2: with No_Soft_Reset set, a PowerState write from D3hot to D0 does not reset the function |
| Recovery time | 10 ms before the next access | PCI PM 1.2, D3hot to D0 |

## The store

Exactly one store: the 16-bit PMCSR word at offset `44`, value `4008`. It
changes only the PowerState field from D3hot to D0. PME stays disabled. No
other configuration register is written; in particular Command stays `0000`.
The lab issues it through mechanism 1 (CF8/CFC), the same path the bound
program's configuration hooks use, through a one-grant window that refuses
every other store.

The generated check `leanos_qotom_broadcom_assign_write` permits the store
only when all of these hold:

1. the generated `qotom-j1900-pci-trust-v1` result for the retained final
   Command vector is one;
2. the D3 record of this boot is the exact successful one;
3. a fresh read shows Command `0000`, PMCSR `400b`, BAR0 `d0700004` and BAR1
   zero; natively the complete header must also match the retained inventory
   header (Command replaced) and the four-entry capability list must be
   unchanged;
4. the store is offset `44`, width 2, value `4008`.

## Post-transition checks

After the 10 ms recovery delay:

1. the complete header again matches the retained one, with Command `0000`
   and the same BARs, and the capability list is unchanged;
2. the PCIe Device Capability and Control/Status words are the retained
   `05908fa0` and `00190000`, so Transactions Pending is clear;
3. PMCSR reads `4008`;
4. two Transactions-Pending-clear samples 10 ms apart, with Command `0000`
   before and after each sample (at most 100 samples);
5. a final read of Command, BAR0, BAR1 and PMCSR.

## When assignment is permitted

`leanos_qotom_broadcom_assign_admission` accepts only when the store was the
permitted one, every post-transition value matches, and the program offered
for binding is assignable:

* its target is exactly `02:00.0`, `14e4:4353`;
* it declares no DMA;
* it may write no configuration dword outside the profile's two backplane
  windows `80` and `ac` (so never Command, PMCSR or a BAR);
* it may set no Command bit other than Memory Space (so never Bus Master).

`qotomBcm43224Policy` itself is assignable (`qotomBcm43224Policy_assignable`).
The variant therefore keeps the initial contract's premise that the
Broadcom is not a bus master: the bound program can enable Memory Space and
nothing else.

Only on acceptance does the lab bind the program to the driver subject. Any
other result prints the record below with a nonzero status and stops at
`qotom-broadcom-assign`. A failed store may have taken effect; the lab does
not return the device to D3hot.

## Theorems

`LeanOS/QotomBroadcomAssignment.lean`:

* `write_one_iff`: the store check returns one exactly for the listed values.
* `write_exact`: the only store it ever permits is the 16-bit PMCSR write of
  `4008`.
* `write_requires_contract`: the store needs the accepted initial contract.
* `admission_one_iff`, `admission_requires_write`: assignment needs the
  permitted store, the post-transition checks and an assignable policy.
* `admission_post_state`: after an accepted assignment the device is in D0
  with Command `0000`, the retained BARs and Transactions Pending clear.
* `admission_policy_no_bus_master`: an accepted program targets `02:00.0`,
  declares no DMA, cannot set Bus Master and cannot write Command or PMCSR.
* `qotomBcm43224Policy_assignable`.

The security claim is SC-QOTOM-BROADCOM-ASSIGNMENT-CONDITIONAL.

## Tests

* `tests/qotom-broadcom-assign.c`: the native sequence with exact argument
  vectors to both checks; every read failure; store and delay failures; a
  device that stays in D3hot; Transactions Pending that never clears; every
  bit of the configuration space it reads; every bit of the D3 record,
  inventory header, capability list, PCIe prior and offered policy.
* `tests/qotom-broadcom-assign-window.c` and `-arm.c`: the one-grant window
  and its arm gate, mutated like the other device windows.
* `tests/qotom-broadcom-assign-admission.c` (run by
  `scripts/check-qotom-pci-final-admission.sh`): the generated exports from
  the same native object as the lab image. Every single-bit mutation of every
  input is refused, except a quiet-poll count still in range and a narrower
  policy. The native sequence with the real exports admits the retained
  values and refuses a rejected contract, a device already in D0 and a policy
  that could set Bus Master.

## Serial record

On success the lab prints, before the `SERVICE grant` line:

```text
LEANOS-LAB/1 BROADCOM-ASSIGN profile=qotom-j1900-pci-trust-v1-bcm43224-assign-v1 device=2:0.0 status=0 contract=1 pmcsr-before=16395 command-before=0 d0-attempted=1 pmcsr-after=16392 command-after=0 bar0=3497000964 bar1=0 polls=2 device-status=25 admitted=1
```

`polls` may be larger than 2 if a sample showed Transactions Pending.
Statuses: 0 accepted; 1 argument; 2 prior; 3 pre-store read or header
mismatch; 4 store refused by the generated check (nothing written); 5 store
failed; 6 delay failed; 7 post-transition header, PCIe or PMCSR mismatch;
8 Transactions Pending not quiet; 9 final read failed; 10 assignment refused
by the generated check; 11 the contract, priors or policy did not arm the
window (nothing read or written).

## Limits

The variant does not establish posted-write drain, TXE-private quiescence or
firmware/SMM noninterference; those stay premises of the initial contract.
It does not prove that configuration reads are faithful or fresh, that the
device obeys Command, or that the Broadcom firmware is stopped. It is not
a VT-d or IOMMU result. It has not run on the hardware yet; the maintainer
steps are in [the WiFi driver notes](wifi-driver.md#maintainer-steps-for-the-capture).
