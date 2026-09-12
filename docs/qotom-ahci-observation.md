# Qotom AHCI capability and control observation

The retained native PCI header identifies SATA at 00:13.0, vendor/device
`8086:0f23`, class/revision `0106010e`, standard type-0 header, Command `0007`,
and ABAR `d0916000`. It is the controller used by the installed FreeBSD disk;
its shutdown needs separate evidence before any DMA quarantine claim.

Intel's [J1900 datasheet, 329670-002](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf)
section 13.5.15 identifies ABAR at configuration offset `0x24` and a 2 KiB
memory resource in AHCI mode. Sections 13.8.1, .2, .4, .5 and .6 identify CAP,
GHC, PI, VS and CAP2 at offsets `0`, `4`, `0xc`, `0x10` and `0x24` respectively.
CAP2.BOH is documented as unsupported. Consequently this first observer does
not assume or access a BIOS/OS handoff register; it records CAP2 for the later
policy alongside the other raw values.

`boot/qotom-ahci-capabilities.h` binds the exact captured PCI identity, class,
header layout, memory-enable bit and ABAR. Five configuration checks precede
five MMIO samples, followed by the same five configuration checks. All failures
publish zero output, including failures after the last MMIO sample. Each raw
MMIO dword is retained unless it is all ones; no version, enabled-port, running,
interrupt or ownership policy is inferred from it. Unrelated live PCI Status
and Command bits are not frozen by the memory-resource binding.

The maximum is 15 reads with no write callback, allocation or polling. Address
selection allows only the five listed dwords and does not authorize mapping.
The caller must bind firmware, the memory resource, UC attributes, root and
alias constraints, and the private read window. Inputs must remain immutable
and nonaliasing, with serialized access. Final configuration agreement is not
an atomic snapshot or continuing firmware exclusion.

Ordinary and sanitizer tests in `scripts/check-pci-capabilities.sh` exercise
all 15 read failures, every bit of initial and refreshed resource/identity
fields, allowed unrelated changes, each raw payload bit, all-ones rejection,
address bounds and invalid arguments. The lab window and arm gate now bind the same PCI header and captured firmware
copies to the validated root. They exclude all present aliases to the mapped
4 KiB page containing the 2 KiB ABAR resource. The temporary leaf is
`80000000d0916019`: supervisor, read-only, NX, with the reviewed UC PAT slot.
Only the five listed dwords can be loaded. Reads restore the exact saved leaf
and invalidate before checking post-read controls; mapping or restoration
interference terminates rather than publishing a value. Failed rearming clears
all saved authority, without performing device access.

Window tests exercise every byte offset in the page, all five permitted loads,
load failure and pre/post-read control or mapping interference. Arm tests cover
all 4096 possible alias leaves, every bound PCI-header bit, changed firmware,
missing callbacks and failed rearming. The native stage now emits one `AHCI-CAPS` result after successful PCIe Device
capture. It disarms the configuration and MMIO contexts before serial output
or a failure terminal. The builder option `--ahci-capabilities` requires
`--pcie-device-observation` and selects `build/qotom-ahci-lab`.

The matching runner option fingerprints the decoder and saves
`ahci-capabilities.json`. The decoder validates the preceding PCIe/USB sequence,
requires the exact bound SATA header for helper results, rejects impossible
native argument/header failures, and preserves raw successful values without
interpreting controller state. Every failure has zero payload, and the actual
AHCI terminal survives projection through the earlier decoders. Synthetic
protected replays cover success, all reachable helper/arm failures, malformed
records, all-ones fields and terminal contradictions.

The [protected physical capture](../hardware/lab/observations/qotom-native-ahci-20260911/README.md)
passed with CAP `c720ff01`, GHC `80000002`, PI `2`, VS `10300`, CAP2 `38`.
It reports AHCI/global interrupts enabled, port 1 implemented, AHCI 1.3 and BOH
clear. FreeBSD recovered automatically with the request consumed. The retained
regression replays the exact values and recovery bytes. Port engine state and
outstanding commands remain unobserved; no SATA write or DMA proof is supplied.
It advances the SATA portion of #330 and #291 without granting boot admission.

## Bounded port 1 observer

`boot/qotom-ahci-port.h` accepts the captured CAP/PI/VS/CAP2 profile, AHCI enabled,
and global interrupts either enabled or disabled. It compares each complete
fresh global snapshot with the supplied prior snapshot; an interrupt-enable
change during observation therefore rejects. It requires prior collection
success before any access and never treats a different implemented-port map
as permission to read another port.

The [Intel datasheet](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf),
sections 13.8.31–.33, .35, .38 and .39, locates port 1 IE, CMD, TFD, SSTS, SACT and CI
at ABAR offsets `194`, `198`, `1a0`, `1a8`, `1b4`, `1b8` (hexadecimal).
The observer samples CMD, IE, TFD, SSTS, SACT, CI, then CMD again. Two complete
15-read global/resource refreshes bracket these seven samples: 37 reads total.
There are no writes, polling, reset or port 0 accesses. Failure zeroes every
output field. Changed command or queue samples remain raw observations rather
than an atomic snapshot, halt, transaction-drain or DMA-containment proof.

Tests check exact access order, all 37 failures, all global-field bit changes
before/after port access, each port payload bit, all-ones rejection, prior
profile rejection, both permitted global-interrupt states, and address bounds.
The dedicated port window admits exactly the six listed addresses through a
read-only, NX, supervisor UC leaf. Its private arm gate validates prior collection
success and the captured single-port profile, then reuses the AHCI firmware,
root, PCI-resource and alias checks without exporting the global reader's
authority. Every failed rearm clears prior authority; no device access occurs
while arming. Read restoration and post-control checks remain mandatory.

Window/arm tests cover every byte offset, all six permitted loads, failed loads,
mapping/control interference, 4096 possible resource aliases, all bound header
bits and prior-global bits, and failed prior statuses. Both accepted global
interrupt states remain covered.

The opt-in `--ahci-port` build requires the global AHCI capture and records all
seven port samples after disarming its access contexts. Local arm failures use
status 8 (global window) or 9 (port window); helper failures remain 3 through 7.
The protected runner fingerprints the port decoder, retains `ahci-port.json`,
and preserves the actual failure terminal while replaying preceding stages.
Decoding rejects missing/duplicate records, malformed values, failed observations
with nonzero payload, all-ones successful samples, mismatched terminals, and
helper observations without the bound prior global profile. Port samples do not
establish an atomic snapshot or DMA quarantine.

The [physical port capture](../hardware/lab/observations/qotom-native-ahci-port-20260911/README.md)
returned status 0 with CMD `6` before and after, IE `0`, TFD `50`, SSTS `123`,
SACT `0` and CI `0` (hexadecimal). Both CMD samples had ST/FRE/CR/FR clear;
command-list and FIS-receive engines reported stopped. No SATA write, stop or
reset was needed for this observation. Global interrupts remained enabled.
The retained protected replay agrees and FreeBSD recovered automatically with
the request consumed. These samples guide a subsequent guarded interrupt/BME
transition; transaction drain, continuing firmware/AP exclusion and whole-profile
integration remain open.

## Bounded global interrupt disable

`boot/qotom-ahci-interrupts.h` requires successful global and port observations
matching the captured stopped/empty port profile, with GHC `80000002`. It
refreshes all 37 global/resource/port reads before writing one DWORD `80000000`
to ABAR+4, immediately reads GHC back, and repeats the complete 37-read collector
against the expected interrupt-disabled globals. Both port snapshots must retain
CMD6/IE0/TFD50/SSTS123/SACT0/CI0/CMD6 (hexadecimal). A changed state rejects.

Intel 329670-002 section 13.8.2 defines GHC.AE at bit31, IE at bit1 and HR at bit0.
The write retains AHCI mode, clears global interrupt enable and leaves reset
unrequested. The helper performs at most 75 reads and one write, with no polling,
port writes, engine stop, reset or BME change. It records whether a write was
attempted and the available before/after control samples, including ambiguous
failed writes; it never retries or restores interrupts as rollback.

Tests cover every read failure, every prior/global/port bit mutation, initial and
final state changes, all immediate readback bit changes, ignored writes and
failed writes with and without effects. The helper still requires a separate
consumed native write window and firmware/root/resource binding before hardware
execution. Interrupt masking does not establish transaction drain, continuing
firmware/AP exclusion or platform admission.

The consumed interrupt window admits only address `d0916004`, value `80000000`
(hexadecimal), through a single trusted DWORD store. Every request consumes its
armed flag, including rejected requests. The mapping uses the AHCI page as RW,
NX, supervisor UC, restores the original leaf exactly, invalidates before and
after the store, and checks control state before returning. Mapping or control
interference terminates; a failed store can still have changed the device.

The arm gate checks both successful prior statuses, the exact globals and
stopped/empty port samples, PCI identity/resource binding, copied firmware,
compiled roots and every possible present AHCI-page alias. Failed rearms revoke
all authority. Arming performs no store, invalidation or device access. Tests
exercise address/value mutations, rejected reuse, every missing callback,
failed stores, restoration interference, all 4096 aliases, bound header bits,
all prior sample bits and failed prior statuses.

The opt-in `--ahci-interrupts` image requires port capture. Native code uses the
existing single-DWORD store primitive and disarms readers and writer before
emitting attempted/before/after fields. Global, port and writer arm failures use
statuses 9, 10 and 11. The protected runner fingerprints its decoder, retains
`ahci-interrupts.json` and preserves the actual terminal after projecting earlier
stages. Decoding requires the successful port prefix and exact stopped/IE-on
profile for helper outcomes. It distinguishes unavailable readback from failed
readback (including all ones) and final-refresh failure after accepted readback.
The [physical interrupt-disable capture](../hardware/lab/observations/qotom-native-ahci-interrupt-20260911/README.md)
reported status 0, attempted 1, GHC `80000002` to `80000000` (hexadecimal), with
both complete refreshes and immediate readback accepted. The retained protected
replay agrees; FreeBSD recovered automatically and independent SSH verified the
consumed request and installed hashes. No SATA BME clear has occurred yet.
Interrupt masking and stopped/empty samples do not establish transaction drain
or continuing firmware/AP exclusion.
