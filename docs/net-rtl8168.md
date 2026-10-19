# RTL8168 wired Ethernet program

`LeanOS/Net/Rtl8168.lean` is a Lean device program for the Qotom's Realtek
RTL8168E-VL controllers (PCI `10ec:8168`). It drives the controller at
01:00.0 — FreeBSD's `re0`, the cabled port — through its 64-bit memory BAR2
(configuration offset 0x18, 4 KiB). It is ported from FreeBSD's BSD-licensed
`re(4)` driver ([sources and hashes](qotom-realtek-state.md)).

The program:

1. checks the controller identity and the 8168E-VL hardware revision in
   `TXCFG`, prints the controller's registers as the previous owner left them
   (the *before* dump, below), and reads the station address;
2. resets the MAC and applies the `re_init_locked` settings for this revision:
   C+ command (`PCI_MRW | MACSTAT_DIS | 1`), station address under the config
   unlock, receive and transmit ring bases, transmit/receive enable,
   `TXCFG_CONFIG`, early-transmit threshold 16, and a receive filter of
   individual and broadcast frames with `EARLYOFF`; interrupts stay masked;
3. waits for link (the PHY autonegotiates by itself);
4. sends an ARP probe for the router 192.168.6.1 — sender address 0.0.0.0, as
   RFC 5227 prescribes for probes, so the program claims no address — up to
   three times, and polls a one-descriptor receive ring for the reply;
5. prints the router's hardware address and the receive counters;
6. runs the [teardown](#teardown), prints the registers it hands back (the
   *after* dump) and clears Bus Master.

Every exit after step 2 enables the transmit and receive engines (no link,
transmit stuck, no reply, success) goes through step 6. Before issue #577 the
failure exits left the engines running.

It needs 8-bit register access (the command, config-unlock, transmit-poll and
media-status registers are bytes), which the bytecode provides as `read8` /
`write8`.

## Teardown

The teardown hands the controller back in the state re(4)'s own `re_stop` and
`re_reset` leave it in. `re_init_locked` runs exactly these two before it
reprograms the chip, and they are what cures the stall when you run
`ifconfig re0 down up`:

1. `re_stop` for CMDSTOP chips, followed exactly: clear only the four accept
   bits of RXCFG (`RX_ALLPHYS | RX_INDIV | RX_MULTI | RX_BROAD`), keeping the
   FIFO, DMA-burst and `EARLYOFF` fields; write `STOPREQ | TE | RE` to the
   command register; poll TXCFG for queue-empty; then wait 1 ms
   (`DELAY(1000)`). re(4) writes nothing else to the command register here.
2. Mask and acknowledge every interrupt (IMR 0, ISR 0xFFFF).
3. Disarm both rings in scratch. Every descriptor is left with EOR only (never
   OWN) and no buffer address, so whichever ring base the controller keeps, it
   finds nothing it is allowed to fill.
4. `re_reset`: write `RST` and poll until it clears.
5. Lock the configuration registers (9346CR = 0).

Like re(4), the teardown never stops on a timeout. A stop timeout prints tag
0x400D. A reset timeout prints 0x400E, and the program then ends with
`resetStuck` (0x7B04) after clearing Bus Master. Any earlier failure code takes
precedence.

The receive ring holds a single descriptor carrying EOR, the same shape as the
transmit ring. The controller goes back to that descriptor after every frame,
so the position it keeps in the receive ring is always descriptor 0
(`Ring.next_one`). Before #577 the receive ring had 16 descriptors, and the
position left behind was the number of frames received, mod 16. The poll
interval is 100 µs, so a frame that arrives while the single descriptor is
still full is rarely dropped. The probe is sent up to three times.

The teardown uses only register writes the policy already admitted (RXCFG,
command, IMR/ISR and 9346CR are outside the address sinks) and scratch
stores. Neither the confinement policy nor the lab kernel's profile changes.

### Register dumps

The program prints each register in the list below twice, as `WIFI <tag>
<value>`. The tag is 0x4100 + offset before the program touches the
controller, and 0x4200 + offset after the teardown:

| Offset | Register | Width |
| --- | --- | --- |
| 0x37 | command (`TE` 0x04, `RE` 0x08, `RST` 0x10, `STOPREQ` 0x80) | 8 |
| 0x3C / 0x3E | IMR / ISR (ISR bit 0x10: receive descriptor unavailable) | 16 |
| 0x40 / 0x44 | TXCFG / RXCFG | 32 |
| 0x4C | missed-packet counter | 32 |
| 0x50 | 9346CR (config lock; locked when the EEM bits 7:6 are clear) | 8 |
| 0x52 / 0x54 / 0x56 | CONFIG1 / CONFIG3 / CONFIG5 (PME, wake-on-LAN) | 8 |
| 0x58 | timer interrupt | 32 |
| 0x6C | PHY status (bit 0x02: link) | 8 |
| 0xDA | maximum receive packet length | 16 |
| 0xE0 | C+ command | 16 |
| 0xEC | early-transmit threshold | 8 |
| 0x10 / 0x14 | DTCCR low / high (tally dump address) | 32 |
| 0x20 / 0x24 | TNPDS low / high (transmit ring base) | 32 |
| 0x28 / 0x2C | THPDS low / high (high-priority ring base) | 32 |
| 0xE4 / 0xE8 | RDSAR low / high (receive ring base) | 32 |

For example, `WIFI 41e4` is RDSAR as FreeBSD or the firmware left it, and
`WIFI 42e4` is RDSAR as the program hands it back. All of these are plain
reads, and reading does not clear any of them.

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
router's address and the counters; `0x41xx` and `0x42xx` are the register
dumps.

Hardware: `hardware/lab/observations/qotom-rtl8168-arp-20260929` — the
workstation captured the probe on the wire, and the router address the
program received matches the workstation's neighbour table.

## FreeBSD's `re0` after a run (issue #577)

### Observation

After the 2026-09-29 program had run, the next FreeBSD boot on the Qotom
brought `re0` up, but its receive side stopped after exactly one pass of its
256-entry ring (input counter stuck at 256). The box was unreachable until
`ifconfig re0 down; ifconfig re0 up`, which runs `re_init` a second time and
restores it. It reproduced on every run. A hardware bisection of the program
(2026-09-29, ten cycles) found:

| Variant | TX/RX engines ever enabled | FreeBSD afterwards |
| --- | --- | --- |
| identity and MAC reads only | no | normal |
| plus the initial MAC reset | no | normal |
| plus C+ command, unlock, station address | no | normal |
| plus ring bases, TXCFG, early-TX threshold | no | normal |
| plus MAR, RXCFG, IMR/ISR, max packet length | no | normal |
| the above, then re(4)'s CMDSTOP stop (STOPREQ with TE and RE) | yes | stalls |
| full program, stop by clearing TE/RE instead of CMDSTOP | yes | stalls |
| full program with a final MAC reset | yes | stalls |

The trigger is enabling the transmit/receive engines at all. Neither a MAC
reset nor the CF9 warm reset between LeanOS and FreeBSD clears the state, and
FreeBSD's second `re_init` does. Workaround in the lab: run `ifconfig re0 down
up` (serial console) after a run of a pre-#577 build. The other device
programs do not affect `re0`.

### Root-cause analysis

This analysis comes from the re(4) sources (releng/15.0, the hashes in
[qotom-realtek-state.md](qotom-realtek-state.md)) and the bisection above. The
mechanism inside the chip is a hypothesis until the
[maintainer steps](#maintainer-hardware-steps) confirm it.

**What FreeBSD sees.** On an 8168 re(4) uses `RL_8169_RX_DESC_CNT` = 256
receive descriptors, and EOR is set on the last one. `re_rx_list_init` sets
the consumer index `rl_rx_prodidx` to 0. `re_rxeof` walks forward from that
index and stops at the first descriptor the chip still owns. After each frame
it re-arms the descriptor (`re_newbuf`, or `re_discard_rxbuf` when it drops
the frame), so neither an mbuf shortage nor a receive error stops the ring.
A lost interrupt does not either: the next frame's interrupt resumes the walk.
For the input counter to stop at exactly 256, the chip must stop completing
descriptor 0 after one full pass of the ring. Its descriptor engine and
re(4)'s `rl_rx_prodidx` disagree about where the ring is.

**The registers are not it.** Every register the program writes is rewritten
by FreeBSD's attach and `re_init_locked` before `RE` is set again. The
bisection rows without TE/RE show the same thing directly: leaving these
values behind is harmless.

| State the program leaves | Rewritten by FreeBSD | Bisection |
| --- | --- | --- |
| RDSAR, TNPDS (low and high) pointing into LeanOS scratch | `re_init_locked` loads its own lists before enabling TE/RE | row 4 normal |
| THPDS, DTCCR | never used by the program; re(4) does not use the high-priority ring | — |
| RXCFG, TXCFG, early-TX threshold, MAR | `re_set_rxmode`, `RL_TXCFG_CONFIG`, `re_init_locked` | rows 4–5 normal |
| IMR 0 / ISR acknowledged | `re_stop` and `re_init_locked` | row 5 normal |
| C+ command 0x0089 | `re_init_locked` writes C+ first | row 3 normal |
| 9346CR | already locked by the program after the station address; re(4) unlocks and relocks it | row 3 normal |
| station address (same value) | `re_init_locked` | row 3 normal |
| maximum receive length 0x600 | `re_init_locked` (`RE_RX_DESC_BUFLEN`) | row 5 normal |
| MAC: `RST` | `re_reset` at attach and in every `re_init_locked` | row 2 normal |
| PHY | not written by the program; `mii_mediachg` at init | — |
| receive descriptors in scratch: all 16 chip-owned (OWN), buffers in scratch | not FreeBSD's memory; nothing rewrites them | see below |

So the residue lives in state that software cannot read or write directly. It
is created only while the receive engine runs, and it survives `RST` and the
warm reset (PERST#). This is plausible for a controller that keeps receiving
for wake-on-LAN on auxiliary power: re(4)'s own shutdown path, `re_setwol`,
arms CONFIG1 PME, CONFIG3 magic packet and CONFIG5 LanWake. Inside the receive
DMA engine, the candidate is the controller's own position in the descriptor
ring.

**The chip's ring position (leading hypothesis).** Suppose the controller
enters FreeBSD's ring at a position `start ≠ 0` kept from the LeanOS run. It
fills descriptors `start..255`, but `re_rxeof` waits at descriptor 0 and sees
nothing. After `256 - start` frames the chip wraps at EOR and completes
descriptor 0. Descriptors `start..255` are still waiting, so FreeBSD consumes
all 256 in one burst, and the chip is back at `start`. The cycle then repeats
every 256 frames. On a quiet lab segment that looks like an input counter
stuck at 256 and a box that does not answer. In the model in
`LeanOS/Net/Rtl8168.lean` (`namespace Ring`):

* `seen_none`: entered at `0 < start < 256`, FreeBSD consumes nothing in the
  first `256 - start` frames;
* `seen_full`: after 256 frames it has consumed exactly 256;
* `next_full_pass`: the chip is then back where it entered;
* `seen_aligned`: entered at 0, FreeBSD consumes every frame as it arrives.

The 2026-09-29 run received one frame, so its 16-descriptor ring left
position 1 (`next_sixteen_observed`, `freebsd_after_observed_run`).

This model fits every bisection row. Without TE/RE (rows 1–5) the position
never moves. Row 6's stop request turns the engines on with nothing to stop
them. Rows 7 and 8 stop without re(4)'s handshake. The pre-#577 program's own
stop deviated from `re_stop` in two ways:

* it wrote RXCFG = 0, which also clears the FIFO and DMA-burst fields, where
  re(4) clears only the four accept bits;
* it wrote 0 to the command register as soon as TXCFG reported queue-empty,
  which was immediately, because the transmit side was already idle. re(4)
  never writes the command register after the stop request and waits 1 ms.

FreeBSD's first `re_init` runs `re_stop` on engines its attach never started,
so it cannot complete a stop of the running receive engine. Its second
`re_init` (down/up) stops engines that FreeBSD started itself, with re(4)'s
handshake, then resets and reloads. That one cures it.

**The alternative.** The controller might instead keep a ring *base*, latched
from RDSAR while the LeanOS ring was installed, and wrap to it at EOR instead
of to FreeBSD's ring. Then FreeBSD would get one gradual pass of 256 frames.
After the wrap the chip would use the LeanOS descriptors. If they are still
chip-owned in RAM (a warm reset keeps memory), it would write frames into
memory FreeBSD now owns. Otherwise it would raise "receive descriptor
unavailable" from then on. The teardown's disarmed rings (step 3) remove the
memory-corruption half of this case. If the
[hardware steps](#maintainer-hardware-steps) show this pattern, the fix is
to restore RDSAR/TNPDS to their pre-program values (the before dump) before
the stop. That writes values outside scratch into address sinks, which the
current confinement forbids. It would need a new executor rule (snapshot the
sinks at program start, allow writing back exactly those values) with its
proofs. This is left as a follow-up, because the bisection shows the register
values themselves are harmless (row 4).

### The fix

[Teardown](#teardown) addresses the leading hypothesis in two independent
ways:

* the one-descriptor receive ring leaves position 0 whatever the run
  received, even if nothing resets the position (`Ring.next_one`,
  `freebsd_after_fixed_run`);
* the stop now follows `re_stop` exactly, so a stop handshake that does reset
  the position can complete, and `re_reset` follows as in `re_init_locked`.

It also disarms both rings and runs on every exit after the enable.
`LeanOS/NegativeFixtures/Rtl8168Teardown.lean` runs the encoded program under
its declared policy in the reference simulator, against a recording
controller model, on both the transmit-stuck and the no-link exits. It checks:

* the exact teardown writes;
* that the command register goes TE|RE → STOPREQ|TE|RE → RST with no 0 in
  between;
* that no descriptor is left chip-owned or names a buffer;
* that Bus Master is cleared last;
* that both dumps are complete;
* statically over the encoded words, that no `fail` or `halt` lies between
  the engine enable and the teardown's reset.

Negative fixtures show that the pre-#577 stop and an exit that skips the
teardown are rejected.

### Maintainer hardware steps

These steps run the new program once and check FreeBSD afterwards without
`down up`. Work on the serial console (ttyu0, 38400 8N1), because `re0` may be
stalled. Ping from the wired workstation (192.168.6.62).

1. **Baseline (FreeBSD, before the run).** As root on the Qotom:

   ```sh
   netstat -I re0 -n -b
   sysctl dev.re.0.stats=1; dmesg | tail -20   # tally counters
   ```

2. **Build and install** the image as in [Trying it](#trying-it) and
   `docs/wifi-driver.md` (Booting the image from the SSD). Keep the serial
   capture (`serial.raw`) of the run. Expect, in order:
   * `WIFI 4137` … `WIFI 41e8`: the before dump (23 records);
   * `WIFI 4004` (link), `WIFI 400c 0x70000000`-style transmit status,
     `WIFI 4007`/`4008` (router address), `WIFI 4009` (frames);
   * no `WIFI 400d` and no `WIFI 400e`;
   * `WIFI 4237` … `WIFI 42e8`: the after dump, with `4237` = 0x00 (TE, RE
     and RST clear), `423c` = 0x0000, and `4250` (9346CR) with the EEM bits
     7:6 clear, so the configuration registers are locked. This chip reads
     `0x10`, because bit 4 stays set whatever the program writes; the before
     dump (`4150`) shows `0x10` too;
   * `WIFI 40ff`, then `WIFI-END status=0`.

   `scripts/run-qotom-recovery-lab.py --scenario watchdog-leanos` checks
   these records, with the protected launch and the recovery, and writes
   `result.json` with `PASS` or `FAIL` and the failed checks (issue #595;
   see [Lab runner results for device
   programs](wifi-driver.md#lab-runner-results-for-device-programs)).

3. **Check FreeBSD after the CF9 reset, without touching `re0`.** On the
   Qotom:

   ```sh
   netstat -I re0 -n -w 1      # leave running; watch the Ipkts column
   ```

   On the workstation:

   ```sh
   ping -c 600 -i 0.2 192.168.6.21
   ```

   **Pass:** replies start within a few seconds and continue, Ipkts climbs
   steadily past 256 (600 echo requests alone exceed one ring), and `ssh
   freebsd@192.168.6.21` works, all without `ifconfig re0 down up`. Then
   record `sysctl dev.re.0.stats=1; dmesg | tail -20` and `netstat -I re0 -n
   -b`.

4. **If it still stalls, record which pattern it is** before you recover with
   `ifconfig re0 down; ifconfig re0 up`:
   * Ipkts stays near 0, then jumps by 256 at once, and later again by 256:
     a ring-position mismatch that the teardown did not clear (leading
     hypothesis);
   * Ipkts climbs 1, 2, … to 256 with replies, then stops for good, and the
     tally's `Rx missed frames` keeps rising: a retained ring base (the
     alternative);
   * anything else: keep `netstat -w 1` and the tally output.

   In each case also record `sysctl dev.re.0.stats=1` (the chip's own `Rx
   frames` against FreeBSD's Ipkts).

5. **Before/after register dumps.** The serial capture of step 2 already holds
   the state FreeBSD's shutdown left (`41xx`) and the state the program hands
   back (`42xx`). Run a second cycle with the same image (arm and run it
   again as in step 2, after step 3), so that its `41xx` dump shows what
   FreeBSD's `re_shutdown` (`re_stop`, `re_setwol`) and the CF9 warm reset
   leave behind:
   * RDSAR (`41e4`) or TNPDS (`4120`) holding an address outside the LeanOS
     scratch (FreeBSD's ring) means these registers survive the warm reset;
   * zeros mean PERST# clears the visible registers, so whatever survives is
     internal state, as the analysis assumes;
   * the command (`4137`), IMR (`413c`) and CONFIG1/3/5 (`4152`, `4154`,
     `4156`) values show whether FreeBSD left wake-on-LAN armed.

   Compare each cycle's `42xx` with its `41xx`, and attach both captures and
   the step 3–4 output to issue #577.

A pass in step 3 confirms the fix for this machine. A stall with the first
pattern refutes "the teardown resets the position". A stall with the second
pattern points to the alternative and its follow-up.
