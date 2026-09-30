# RTL8168 wired Ethernet program

`LeanOS/Net/Rtl8168.lean` is a Lean device program for the Qotom's Realtek
RTL8168E-VL controllers (PCI `10ec:8168`). It drives the controller at
01:00.0 — FreeBSD's `re0`, the cabled port — through its 64-bit memory BAR2
(configuration offset 0x18, 4 KiB). It is ported from FreeBSD's BSD-licensed
`re(4)` driver ([sources and hashes](qotom-realtek-state.md)).

The program:

1. checks the controller identity and the 8168E-VL hardware revision in
   `TXCFG`, and reads the station address;
2. resets the MAC and applies the `re_init_locked` settings for this revision:
   C+ command (`PCI_MRW | MACSTAT_DIS | 1`), station address under the config
   unlock, receive and transmit ring bases, transmit/receive enable,
   `TXCFG_CONFIG`, early-transmit threshold 16, and a receive filter of
   individual and broadcast frames with `EARLYOFF`; interrupts stay masked;
3. waits for link (the PHY autonegotiates by itself);
4. sends an ARP probe for the router 192.168.6.1 — sender address 0.0.0.0, as
   RFC 5227 prescribes for probes, so the program claims no address — up to
   three times, and polls a 16-entry receive ring for the reply;
5. prints the router's hardware address and the receive counters, stops the
   MAC (`CMDSTOP`, waiting for the transmit queue to drain) and clears Bus
   Master.

It needs 8-bit register access (the command, config-unlock, transmit-poll and
media-status registers are bytes), which the bytecode provides as `read8` /
`write8`.

## Confinement

The program is admitted under `qotomRtl8168Policy`
([device-program confinement](device-program-confinement.md)): the BAR2
window, configuration reads of identity and command only, no configuration
writes, Memory Space and Bus Master (and clearing Bus Master), and DMA into
scratch. The transmit, high-priority and receive ring bases and the
tally-counter dump address are address sinks, so each can only point into
scratch. The buffer pointers inside the descriptors fall under the J1900 DMA
assumption of [ADR 0021](adr/0021-j1900-device-dma-destinations.md).

## Trying it

```sh
lake exe leanos-wifi-gen rtl8168-arp build/wifi/rtl.bin
python3 scripts/build-qotom-recovery-lab.py --prepared-repo . --lab-program build/wifi/rtl.bin
```

then install and boot the image as in `docs/wifi-driver.md`. Print tags
`0x40xx` report the station address, media status, transmit status, the
router's address and the counters.

Hardware: `hardware/lab/observations/qotom-rtl8168-arp-20260929` — the
workstation captured the probe on the wire, and the router address the
program received matches the workstation's neighbour table.

## Known issue: FreeBSD's `re0` after a run

After this program has run, the next FreeBSD boot on the Qotom brings `re0`
up, but its receive side stops after exactly one pass of its 256-entry ring
(input counter stuck at 256); the box is unreachable until
`ifconfig re0 down; ifconfig re0 up`, which runs `re_init` a second time and
restores it. It reproduces on every run. A hardware bisection of the
program (2026-09-29, ten cycles) found:

| Variant | TX/RX engines ever enabled | FreeBSD afterwards |
| --- | --- | --- |
| identity and MAC reads only | no | normal |
| plus the initial MAC reset | no | normal |
| plus C+ command, unlock, station address | no | normal |
| plus ring bases, TXCFG, early-TX threshold | no | normal |
| plus MAR, RXCFG, IMR/ISR, max packet length | no | normal |
| the above, then re(4)'s CMDSTOP stop (`STOPREQ | TE | RE`) | yes | stalls |
| full program, stop by clearing TE/RE instead of CMDSTOP | yes | stalls |
| full program with a final MAC reset | yes | stalls |

So the trigger is enabling the transmit/receive engines at all; neither a
MAC reset nor the CF9 warm reset between LeanOS and FreeBSD clears the
state, and FreeBSD's second `re_init` does. The root cause is not
established. Workaround in the lab: run `ifconfig re0 down up` (serial
console) after a run of this program. The other device programs do not
affect `re0`.
