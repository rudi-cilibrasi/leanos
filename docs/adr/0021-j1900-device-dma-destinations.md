# ADR 0021: Device DMA destinations on the Qotom J1900

## Status

Accepted. Resolves issue #448 through its fallback: a partial, proved
mitigation plus a recorded assumption.

## Context

The J1900 has no IOMMU: the retained ACPI tables have no DMAR table and the
platform profile marks VT-d unavailable
([Qotom PCI final admission](../qotom-pci-final-admission.md)). Once a
device may master the bus, nothing in hardware limits where it reads or
writes memory.

Two device programs run in the lab kernel
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

A full proof that every pointer the controller follows lies in scratch needs
a model of each descriptor format the controller interprets, together with
the TRB type that decides whether a parameter is a pointer. A program writing
a forged constant into a TRB field is indistinguishable, to an effect-level
checker, from one writing an ordinary parameter.

## Decision

1. **WiFi: no bus mastering at all.** `qotomBcm43224Policy` admits no DMA,
   and its command-register rule lets the program clear Bus Master but never
   set it (`qotomBcm43224Policy_no_bus_master`). The program clears it, so
   even a BIOS that left it on cannot let the card master the bus while the
   program runs. This holds on the hardware
   (`hardware/lab/observations/qotom-device-confinement-20260929`, and with Bus Master explicitly cleared in `qotom-device-dma-sinks-20260929`).
2. **xHCI root registers: proved.** A policy may name *address sinks*: the
   low dwords of 64-bit MMIO address registers. A write that touches a sink
   is admitted only as `write32`/`write32At` of a value inside scratch
   (`value - phys(0) < scratchBytes`) for the low dword, or zero for the high
   dword; 16-bit writes, FIFO and blob streams into a sink are refused. The
   simulator and the C executor both enforce this (status `policy`), the
   `guard` monitor flags any other sink write, and `run_confined` /
   `run_declared_confined` therefore cover it. `qotomXhciPolicy` names CRCR,
   DCBAAP, ERSTBA and ERDP, and the lab kernel refuses an xHCI image that
   declares fewer sinks.
3. **xHCI descriptors: assumed.** That every pointer the program stores in
   scratch descriptors is a scratch bus address is an **unproved trusted
   assumption**. It is mitigated by the program's structure — every such
   pointer is written by `storePhys64` or by `physAddr` plus a bounded ring
   offset — and by review, and is listed in the README's trusted-boundary
   paragraph.

## Residual risk

A defect in the xHCI program, or a hostile program admitted under the xHCI
policy, can store any 32-bit address in a descriptor and make the controller
read or write that physical memory, including kernel memory. The sinks
narrow this to data the program itself places in scratch; they do not close
it. Only the xHCI policy admits DMA, and the lab kernel only runs images
whose declared policy fits its profile table.

## Consequences and follow-up

* The negative fixtures reject a forged DCBAAP address, register-indirect and
  off-by-one variants, a nonzero high dword and partial or streamed sink
  writes, and prove the policy sinks equal the driver's register constants.
* Differential fuzzing covers the sink checks, and the mutation set includes
  sink mutants.
* Closing the gap needs either a descriptor-level model (checked descriptor
  builders whose pointer fields can only come from `physAddr`, plus an
  analysis that no other store reaches a pointer field), or an IOMMU platform.
  Revisit before a DMA-capable program runs on behalf of a kernel subject
  (#449) or a second DMA driver is added (#452).
