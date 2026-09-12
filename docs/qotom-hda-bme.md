# Qotom HDA bus-master disable

The native HDA state capture reports CORBCTL/RIRBCTL/DPLBASE zero and all eight
stream control/status words `00040000` (hexadecimal), with successful global
and resource checks. PCI Command still reports `0006`. This candidate clears
only BME while retaining MMIO decoding for final state verification.

[Intel 329670-002](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf)
section 15.5.3 defines the HDA Command register at 00:1b.0 offset 4 as a 16-bit
register, with BME at bit 2 and MSE at bit 1. The adjacent Status register is
separate. The single word write of `0002` avoids writing its status bits.

The helper requires successful preceding global/state outcomes, the exact
GCTL1/GCAP4401/version1.0/INTCTL0 profile, the captured stopped/empty state and
initial Command `0006`. It performs a complete 47-read state refresh, verifies
that state and Command, attempts one word write, checks immediate readback,
performs the complete 47-read final refresh, then reads Command again. The bound
is 97 reads and one write. No ring, stream or position register is written;
there is no stop, reset, polling, retry or rollback.

Failed writes may have effects. The result retains attempted/before/after
observations, including actual differing readback when available. Errors before
the write publish zero. Final failures preserve the observed write/readback;
they do not restore bus mastering. Neither Command readback nor sequential
stopped-state samples establish transaction drain, continuing firmware/AP
exclusion or system-wide DMA containment. Whole-platform admission remains open.

Tests cover all 97 read failures, every prior/global/state/Command bit, raw PCI
Status preservation, ignored writes, failed writes with and without effects,
resource drift, post-write restart, BME reassertion and missing inputs. Native
mapping, emission and physical capture remain pending.
