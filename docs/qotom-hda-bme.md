# Qotom HDA bus-master disable

The native HDA state capture reports CORBCTL/RIRBCTL/DPLBASE zero and all eight
stream control/status words `00040000` (hexadecimal), with successful global
and resource checks. PCI Command still reports `0006`. The bounded helper clears
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
resource drift, post-write restart, BME reassertion and missing inputs. The retained physical capture below passed.

## Consumed write window

The separate writer accepts only 00:1b.0 offset 4 and word value `0002`. Every
request consumes its armed flag, including rejected requests. It maps ECAM
page `e00d8000` with leaf `80000000e00d801b` (RW/NX/supervisor UC), invokes the
trusted single-word store, restores the exact original leaf, invalidates on
both transitions and checks final controls. Interference terminates after
cleanup. Reuse and every other word value are rejected without a store.

Arming binds successful global and state observations, exact stopped samples,
Command `0006`, identity/resource, copied firmware and roots. It rejects every
low-memory alias across the 16 KiB HDA resource. All rejected rearms clear old
authority; arming performs no device access. Tests cover all alternative word
values, BDF/offset changes, callback omissions, invalid apertures, failed stores,
restoration interference, every bound input bit and all four pages of aliases.

## Native capture

The opt-in `--hda-bme` build requires `--hda-state`. Native code arms the global
reader, state reader and consumed writer (local failures 9, 10 and 11), invokes
the helper and disarms all contexts before `HDA-BME`. The trusted word-store
primitive is reused from the earlier BME stages. Nonzero outcomes terminate
with `qotom-hda-bme`.

The protected runner fingerprints the BME decoder, retains `hda-bme.json` and
restores the actual terminal after earlier projections. Helper outcomes require
the preceding stopped-state tuple and captured Command `0006`. Exact framing,
bounded word values, attempted/before/after consistency and matching terminal
are checked; final failures may retain changed Command. Failed writes are not
replayed or silently treated as having no effect.

## Physical result

The [protected native capture](../hardware/lab/observations/qotom-native-hda-bme-20260911)
reports status 0, attempted 1 and Command `0006` to `0002`. Both full state
refreshes and immediate/final Command checks passed. FreeBSD recovered
automatically with the request consumed; independent SSH verified BIOS boot
and installed hashes. The 59-file evidence manifest and retained replay passed.

All 55 protected capture groups passed before the clean build. All 123 build
hashes, eight-site MSR-write audit, single-word store disassembly and QEMU
foreign-firmware rejection passed. This is one controller transition; the
whole-platform quarantine and production admission requirements remain open.
