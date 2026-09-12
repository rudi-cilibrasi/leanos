# Qotom Realtek engine-state observation

The native PCI capture identifies two revision-07 10ec:8168 endpoints at
01:00.0 and 03:00.0. FreeBSD after the root-port experiment reports chip revision
`0x2c800000` for both. This OS observation selects a candidate; LeanOS must read
and validate the revision itself before using any revision-specific operation.

The FreeBSD 15.0 driver identifies this as RTL8168E-VL, selects memory BAR2 for
8168 controllers, and sets CMDSTOP plus CMDSTOP_WAIT_TXQ for this revision.
Its stop path disables receive acceptance, requests stop with TX/RX enable,
waits for TXCFG queue-empty, delays, then masks and acknowledges interrupts.
A timeout is logged rather than returned as a hard failure, so that routine
cannot be copied as a fail-closed quarantine proof.

Primary implementation references:

- [FreeBSD releng/15.0 if_re.c](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/dev/re/if_re.c): BAR selection, revision dispatch and `re_stop`.
- [FreeBSD releng/15.0 if_rlreg.h](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/dev/rl/if_rlreg.h): register widths/offsets and revision mask.
- [Linux v6.12 r8169_main.c](https://github.com/torvalds/linux/blob/v6.12/drivers/net/ethernet/realtek/r8169_main.c): independent version-34 identification; later-chip FIFO routines must not be applied to version 34.

Inspected source SHA256 values, in that order:

```text
ac3049b455f9d21925fc60399fb703957ba2401fc604e503dcf73aca170e5286
c55abe699b73ac241a99c6224adad8ca46c8c5de1e253b6af1f39ca171d08f8e
c7d8ba27d0266db93d5177388b95a688d825ec7244e674a5fd2f2f10d74a0417
```

## Bounded helper

`boot/qotom-realtek-state.h` binds bus 1 or 3, device/function zero, exact
identity/class/revision, type-0 layout, Command 0007 and both 64-bit memory BARs.
BAR2 is d0804000/d0604000 (4 KiB); BAR4 is d0800000/d0600000 (16 KiB).
Eight configuration reads bracket six typed MMIO reads, totaling 22:

| Order | Register | Offset | Width |
| --- | --- | --- | --- |
| 1 | TXCFG, including hardware revision | 40h | 32 bits |
| 2 | Command | 37h | 8 bits |
| 3 | Interrupt mask | 3ch | 16 bits |
| 4 | Receive configuration | 44h | 32 bits |
| 5 | Command | 37h | 8 bits |
| 6 | TXCFG, including hardware revision | 40h | 32 bits |

Both TXCFG samples must satisfy mask 7cc00000 = 2c800000. Both Command samples
must have Reset clear; other engine state is retained without claiming stopped.
All-ones or improperly extended narrow values reject. Configuration refreshes
bind Command, identity, class/revision, header type and all four memory BAR
DWORDs; asynchronous PCI Status and cache/latency fields are not compared.
Every failure publishes a zero observation. No writes, interrupt status reads,
acknowledgements, polling, reset or shutdown occur.

Statuses are 0 success, 1 argument, 2 initial header, 3 config read, 4 drift,
5 MMIO read, 6 all-ones absence, 7 width, 8 chip revision, 9 reset active.
The address selector grants no authority. Native integration must bind the
selected endpoint, upstream routing, serialized immutable/nonaliasing inputs,
firmware/root controls and all aliases of both resource apertures before access.

The unit tests use modeled engine values. They check both endpoints, exact read
order, every read failure, all compared config bits in both refreshes, ignored
Status/cache fields, chip-revision masks, reset, width, absence and address/width
selection. Native integration and protected decoding are described below; the
retained physical result validates this bounded observation separately.

The later shutdown contract still needs bounded time and failure handling,
interrupt/MSI/MSI-X treatment, BME control and outstanding traffic semantics.
Root-port BME gating and these samples alone do not establish endpoint drain,
continuing firmware exclusion or admission for issues #330 and #291.

## Physical result

The [retained capture](../hardware/lab/observations/qotom-native-realtek-state-20260911/README.md)
contains successful observations for both endpoints. Each returned stable TXCFG
`2f900d00`, Command `00`, interrupt mask `0000`, receive configuration
`0002ff0e`, Command `00` and TXCFG `2f900d00` (hexadecimal). Both complete live
bridge refreshes passed around each endpoint observation.

The expected terminal remains `qotom-platform-pending`. FreeBSD recovered with
a changed boot time and consumed request; independent SSH verified BIOS boot,
the installed hashes and removal of the read-only mount. The retained replay
checks the complete timed serial classification, exact records, terminal, quiet
interval and recovery metadata. This validates the bounded observations and
does not establish engine shutdown or platform admission.

## Bound register window

The read window binds bus 1 or 3 and permits only the four documented register
addresses at their exact widths. It maps the selected BAR2 page as supervisor,
read-only, NX, UC (leaf 80000000d0804019 or 80000000d0604019), performs one typed
load, restores the exact previous leaf, invalidates it and rechecks controls
before publishing the sampled value. Mapping or restoration interference is
terminal. Requests for the other endpoint are rejected before mapping.

Arming clears the prior bus and all mapping authority first. It validates the
endpoint header, copied firmware, active root and both control samples, then
rejects every present alias to all five pages covered by BAR2 and BAR4. Only
after all checks does it publish the selected bus and armed state. It performs
no device access. Upstream bridge routing must additionally be refreshed in the
native collector before MMIO; this arming helper does not observe live routing.

Window tests cover both endpoints and every address/width combination within
each page, callbacks, invalid apertures, wrong buses, failed loads, exact restore
and terminal interference. Arming tests cover all 4096 alias positions for all
five resource pages of both endpoints, header bits, firmware/root changes,
rejected rearm, missing callbacks and both failed/mismatched control samples.

## Live bridge refresh

`boot/qotom-realtek-route.h` wraps the endpoint collector with complete live
bridge header and PCIe capability refreshes. Bus 1 binds root function 0 and
bus 3 binds root function 2. The initial bridge must describe exactly that
secondary/subordinate bus, the captured memory window covering both endpoint
BARs and the disabled prefetchable window. It also requires the preceding
successful root-port result: attempted 1, Command 0007 to 0003.

The initial bridge header is preserved. A private copy sets expected Command
to 0003 for each live refresh. The existing root-port refresh verifies routing,
identity, current Command, complete capability list and Device registers; it
rejects nonzero Device Control or sampled Transactions Pending. Two 34-read
native bridge refreshes bracket the 22-read endpoint observation (90 reads;
conservative maximum 266). The first failure stops, and a final bridge failure
publishes a zero result even after successful endpoint samples.

Wrapper statuses add 10 for route/prior binding, 11 for the first bridge refresh
and 12 for the last. Tests check both paths, exact 90-read order, every failed
read, every bridge header bit at both refreshes, pending transactions, list
mutation, invalid routing, prior-result mutations and missing inputs. These
remain sequential observations, not proof of atomic routing or transaction
drain. Native wiring is described below, and the retained physical validation
is described above.

## Native capture and decoding

The opt-in `--realtek-state` build requires `--rootport-bme` and retains all four
successful root-port results before running this stage. It clears the result
array before every root-port pass, and only successful transitions populate it.
The Realtek stage executes index 13/bus 1/root index 6, then index 15/bus 3/root
index 8. Local count/index/arm rejection is status 13. Each observer is disarmed
before output, and the first nonzero result halts without accessing the next
endpoint. The native test uses the actual arm, route/helper and window with
modeled device callbacks; all 180 read-failure positions, swapped endpoint
indices, bad prior transitions and count rejection are covered.

The runner fingerprints the decoder, stores `realtek-state.json` and restores
the actual terminal reason after projecting earlier stages. Decoding requires
the complete successful root-port prefix, ordered Realtek indices and either
two successes or a prefix ending at the first failure. It checks initial
endpoint/bridge bindings, field widths, revision/reset constraints, zero failed
output and the matching terminal. Argument/header statuses 1 and 2 are impossible
through this native path and reject. This records state without claiming device
shutdown, DMA containment or whole-platform admission.
