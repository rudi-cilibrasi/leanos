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
establish an atomic snapshot or DMA quarantine. A physical port capture remains
necessary before this can guide device shutdown.
