# ADR 0021: Device DMA destinations on the Qotom J1900

## Status

Accepted. Resolves issue #448 through its fallback: a partial, proved
mitigation plus a recorded assumption. Amended for issue #495: the xHCI
descriptor pointers are now proved under a named assumption about the xHCI
specification. Amended for issue #640: so are the Qotom AHCI identify and
RTL8168 programs' descriptor pointers, so no DMA pointer of a Qotom device
program is an unproved trusted assumption any more; each map's completeness
is a named assumption about its controller.

## Context

The J1900 has no IOMMU: the retained ACPI tables have no DMAR table and the
platform profile marks VT-d unavailable
([Qotom PCI final admission](../qotom-pci-final-admission.md)). Once a
device may master the bus, nothing in hardware limits where it reads or
writes memory.

Four device programs run in the lab kernel
([device-program confinement](../device-program-confinement.md)):

* The **BCM43224 WiFi** program moves every frame by programmed I/O. It never
  needs to master the bus.
* The **xHCI keyboard** program must let the controller master the bus. It
  learns scratch bus addresses through `physAddr` and gives them to the
  controller two ways: in four root address registers (CRCR, DCBAAP,
  ERSTBA, ERDP), and inside descriptors it builds in scratch (DCBAA and
  scratchpad-array entries, the ERST entry, TRB parameters such as the Input
  Context pointer and data-buffer pointers, Link TRBs, and endpoint-context
  dequeue pointers). The controller follows every one of these pointers.
* The **AHCI identify** program (`LeanOS/Storage/Ahci.lean`) masters the bus
  through port 1's command list and received-FIS area (PxCLB, PxFB), the
  command header's command-table address (CTBA) and the PRD's data-buffer
  address.
* The **RTL8168 ARP** program (`LeanOS/Net/Rtl8168.lean`) masters the bus
  through the descriptor-ring base registers (TNPDS, THPDS, RDSAR), the
  tally-dump address (DTCCR) and the buffer address in each transmit and
  receive descriptor.

`qotomXhciPolicy`, `q35XhciPolicy`, `qotomAhciPolicy` and
`qotomRtl8168Policy` all admit DMA (`dma := true`).

Whether a value the program stores in scratch is a pointer depends on the
descriptor format the controller interprets, and for a TRB on its type: a
Setup Stage TRB carries the 8-byte setup packet inline, while Normal, Data
Stage, Link and Address Device / Configure Endpoint TRBs carry pointers. A
program writing a forged constant into a TRB field is indistinguishable, to
an effect-level checker, from one writing an ordinary parameter.

## Decision

1. **WiFi: no bus mastering at all.** `qotomBcm43224Policy` admits no DMA,
   and its command-register rule lets the program clear Bus Master but never
   set it (`qotomBcm43224Policy_no_bus_master`). The program clears it, so
   even a BIOS that left it on cannot let the card master the bus while the
   program runs. This holds on the hardware
   (`hardware/lab/observations/qotom-device-confinement-20260929`, and with Bus Master explicitly cleared in `qotom-device-dma-sinks-20260929`).
2. **Root address registers: proved, for every DMA program.** A policy may
   name *address sinks*: the low dwords of 64-bit MMIO address registers. A
   write that touches a sink is admitted only as `write32`/`write32At` of a
   value inside scratch (`value - phys(0) < scratchBytes`) for the low dword,
   or zero for the high dword; 16-bit and 8-bit writes, FIFO and blob streams
   into a sink are refused. The simulator and the C executor both enforce
   this (status `policy`), the `guard` monitor flags any other sink write,
   and `run_confined` / `run_declared_confined` therefore cover it.
   `qotomXhciPolicy` and `q35XhciPolicy` name CRCR, DCBAAP, ERSTBA and ERDP;
   `qotomAhciPolicy` names PxCLB and PxFB; `qotomRtl8168Policy` names DTCCR,
   TNPDS, THPDS and RDSAR. The lab kernel refuses an image that declares
   fewer sinks than its profile.
3. **xHCI descriptors: proved (issue #495).** A policy may carry a typed
   *descriptor map* (`Policy.descriptors`): scratch regions of 64-bit pointer
   fields, or of 16-byte TRBs whose parameter is a pointer unless the TRB
   type is 0 (reserved) or 2 (Setup Stage, immediate data). Every scratch
   store (`memStore`) must leave every field of the map holding zero or a
   bus address inside scratch (`Sim.descOk`); FIFO input (`fifoIn`) into a
   region is refused. The simulator and the C executor enforce this (status
   `policy`); the C executor re-checks the map only after a store that
   touches a region, which is equivalent while the map holds and is covered
   by differential fuzzing and its mutation set. `run_declared_descriptors`
   and `run_admissible_descriptors` (security claim
   SC-DEVICE-PROGRAM-DESCRIPTOR-POINTERS) prove that, from zeroed scratch
   with a fixed scratch bus address, the map holds only such values in every
   reachable state, for any program that declares the policy — and
   `admissible` requires any policy with a map to be declared. The xHCI
   driver's map (`LeanOS.Usb.Xhci.descriptorMap`, equal by `decide` to the
   maps in `qotomXhciPolicy` and `q35XhciPolicy`, i.e. for both
   `Xhci.Layout`s) covers:
   * the DCBAA (MaxSlotsEn + 1 = 5 entries: the scratchpad-array pointer and
     each slot's output context);
   * the scratchpad array (16 entries on Bay Trail; none on qemu-xhci);
   * the ERST entry's segment base;
   * the TR Dequeue Pointer of every endpoint context (2–32) in the input
     context, so EP0 and the keyboard's interrupt endpoint;
   * every TRB of the command ring, the four EP0 transfer rings and the
     interrupt IN ring: Address Device and Configure Endpoint Input Context
     pointers, Data Stage and Normal TRB buffers, and Link TRBs. Enable Slot,
     Disable Slot and Status Stage TRBs carry zero parameters, which pass.

   The driver's `enqueue` first resets the slot's control dword to type 0
   with the stale cycle bit, so a parameter is never rewritten while the slot
   is typed as a pointer TRB. The negative fixtures show that a forged Input
   Context pointer in an Address Device TRB, a forged Normal TRB buffer, a
   nonzero Data Stage high dword, rewriting a handed-over TRB's buffer,
   forged DCBAA, ERST and dequeue pointers, a byte store that moves a pointer
   out of scratch, and FIFO input into a ring all stop with `policy`, while
   the driver's own stores and an arbitrary Setup Stage packet pass.

   **Named assumption.** That the map lists every scratch field the
   controller dereferences — the DCBAA, scratchpad, ERST, endpoint-context
   and TRB formats of xHCI 1.1 §6, and that TRB types 0 and 2 carry no
   pointer parameter — is an assumption about the specification, not
   proved. So is the controller's behaviour: the output contexts and event
   ring, which the controller itself writes, are outside the map, and a
   controller that DMA-writes into the map is not modelled.
4. **AHCI and RTL8168 descriptors: proved (issues #496 and #640).** The q35
   one-sector program of the `ahci-service` image (`LeanOS.Storage.AhciRead`,
   issue #496) declares `q35AhciPolicy`, whose descriptor map names the CTBA
   of all 32 command headers and the data base of the 40 PRDs before its data
   buffer. On the Qotom (issue #640):
   * `qotomAhciPolicy` carries the identify program's map
     (`LeanOS.Storage.Ahci.descriptorMap`): the CTBA of all 32 command headers
     and the data base of the 120 PRD slots between the PRDT and the IDENTIFY
     buffer;
   * `qotomRtl8168Policy` carries the ARP program's map
     (`LeanOS.Net.Rtl8168.descriptorMap`): the buffer address of every
     16-byte descriptor slot of the receive ring area (16 slots, up to the
     transmit ring) and of the transmit ring area (240 slots, up to the
     receive buffers). Each ring holds one descriptor carrying EOR; the other
     slots are mapped so that a descriptor written without EOR still leads
     the controller only to checked buffer fields within those areas.

   Each map equals its driver's by `decide`, both programs are admissible
   under the policies they declare, and `run_admissible_descriptors` covers
   their command-table, PRD and ring buffer pointers. The lab kernel's
   profiles carry the same maps, so it refuses an image that declares less.
   The negative fixtures show that the drivers' own descriptor stores pass,
   and that a forged CTBA in the first or last command header, a forged PRD
   data base in the first or last slot, a forged receive or transmit buffer
   in descriptor 0 or the last slot of either ring area, and a nonzero high
   dword all stop with `policy`.

   **Named assumptions.** Each map lists every scratch pointer its controller
   follows: for AHCI, for the commands the program issues (AHCI 1.3.1
   §4.2.2–4.2.3; one header, PRDTL 1), so a program that wrote a larger
   PRDTL could point the controller at PRDs past the map; for the RTL8168,
   the descriptor format of `RL_RDESC_*`/`RL_TDESC_*` (a command/status
   dword, a VLAN dword, then the 64-bit buffer address), and that the
   controller walks no further than the mapped slots from the ring bases the
   program programs. As for xHCI, the sinks bound the ring and command-list
   bases to scratch, not to the mapped structures, so a hostile program that
   moved them elsewhere in scratch would leave the map; and a controller that
   DMA-writes into a mapped field is not modelled. On q35 the VT-d grant (one
   scratch page) bounds the AHCI controller independently.

## Residual risk

A store of an address outside scratch into a mapped descriptor field is now
refused for the xHCI, AHCI and RTL8168 programs, provided each map matches its
controller; a pointer field a map misses, or a structure a hostile program
moves elsewhere in scratch, would reopen it. The sinks and maps narrow DMA to
data the program itself places in scratch, they say nothing about what a
controller does with it. The lab kernel only runs images whose declared
policy fits its profile table, which includes every profile sink and
descriptor region.

## Consequences and follow-up

* The negative fixtures reject a forged DCBAAP address, register-indirect and
  off-by-one variants, a nonzero high dword and partial or streamed sink
  writes, prove the policy sinks equal the driver's register constants and
  every descriptor map equals its driver's, and reject the descriptor
  mutants listed above.
* Differential fuzzing covers the sink and descriptor checks (random policies
  carry random descriptor maps), and the mutation set includes sink and
  descriptor mutants.
* That every reachable run of the keyboard program passes the descriptor
  check is not proved; the `device-service` QEMU scenario runs it under the
  check, and the Qotom keyboard lab exercises the Bay Trail layout.
* The Qotom AHCI identify and RTL8168 ARP programs ran on the hardware
  under their maps with unchanged results (issue #640,
  [`qotom-descriptor-maps-20261110`](../../hardware/lab/observations/qotom-descriptor-maps-20261110/README.md)).
  The RTL8168's after-run dump shows its ring bases at exactly the mapped
  rings.
* Next: an IOMMU platform, or pinning each ring and command-list base to its
  mapped structure rather than to scratch.
