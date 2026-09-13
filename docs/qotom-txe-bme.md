# Qotom TXE host-visible bus-master transition

This diagnostic follows the retained graphics BME stage and tests the final
initially BME-set PCI function, TXE at `00:1a.0`. It refreshes the two raw TXE
firmware-status DWORDs, requires them to match the earlier observation, changes
PCI Command from `0106` to `0102` with one 16-bit write, verifies immediate
readback, and repeats the complete firmware-status and identity refresh. Memory
decode and SERR# Enable remain set.

The helper is bounded to 23 configuration reads and one exact write. A private
single-use window authorizes only `00:1a.0` offset 4 value `0102`; it temporarily
maps that ECAM page writable, supervisor-only, NX and uncacheable, then restores
the prior mapping and rechecks the active root. Every rejected rearm revokes the
old authority. A failed store may have changed hardware and is terminal.

Intel document 329670-002 section 16.1.1 states that TXE has a multiple-context
DMA engine which accesses system memory and is programmable only by the TXE CPU.
The public datasheet does not define the host-visible TXE PCI Command register
or state that its BME bit gates this private engine. Linux's MEI TXE driver also
does not offer a host-observable whole-engine stop or drain result. Therefore a
successful `0106` to `0102` readback establishes only the ordinary PCI function
permission. It must remain separate from any claim that TXE-private DMA stopped,
transactions drained, or firmware was excluded.

The initial Qotom hardware profile consequently needs an explicit trusted
firmware/TXE noninterference assumption over the bounded CPL3 experiment. The
assumption must say that TXE firmware does not access LeanOS subject, kernel,
page-table, evidence or copy-window frames during the interval. This diagnostic
can add supporting state evidence but cannot prove that assumption.

The opt-in `--txe-bme` image requires `--graphics-bme`. Success emits:

```text
LEANOS-LAB/1 TXE-BME profile=qotom-txe-host-bme-v1 index=4 status=0 attempted=1 before=262 after=258
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
```

The decimal values are `0106` and `0102` hexadecimal. Capture decoding records
`host_visible_bme_cleared=true` while keeping `txe_private_dma_stopped`,
`transaction_drain_established`, `firmware_exclusion_established`, and
`dma_quarantine_established` false.
