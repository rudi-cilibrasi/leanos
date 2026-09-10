# Qotom command and readback observations

The all-zero Command proposal is not a usable physical Qotom policy: host bridge and
LPC Command registers have read-only enabled bits. See
[qotom-lpc-command-constraint.md](qotom-lpc-command-constraint.md).
The synthetic accepted traces below do not establish hardware realizability.

`LeanOS.QotomPCIQuarantineObservation` checks an ordered trace against the
complete captured AHCI inventory from `QotomPCIInventory`. It is a prerequisite
for the quarantine adapter in issue #330, not production admission or a proof
that the board cannot perform DMA.

The proposed order visits downstream endpoints, then bus-zero endpoints, then
bridges. Each of the fifteen trace slots records a write followed by a complete
configuration-header readback. The checker requires offset 4, width 2 and value
zero: a Command word write, without writing the adjacent Status word. It checks
that the write target matches the readback address, decodes the raw header,
compares identity and routing with the expected inventory entry, and requires
a zero Command readback. Count, write, target, decode, inventory and command
errors retain their trace index where applicable.

Successful checking preserves the supplied trace exactly, including its order
and every raw readback field. Its witness contains exactly fifteen steps, each
with a decoded header, the stated write shape, and zero Command. This does not
prove that an adapter actually performed those operations, enumerated every
function, waited for outstanding transactions, or prevented later device state
changes. BARs and forwarding windows remain raw observations; this checker does
not certify them as safe. It also does not bind an initial snapshot or select
the complete physical platform strategy.

The hosted export `leanos_qotom_pci_quarantine_observe` takes a declared count
and a consumed Lean array. It requires count 15 and exactly 375 words before
reading slots. Each 25-word slot contains write BDF, offset, width, value,
readback BDF, and sixteen raw dwords. Success is 1; count and size errors are
0x10000 and 0x10001. Indexed write, target, inventory and command errors use
0x20000, 0x30000, 0x50000 and 0x60000 plus the index. Header errors use 0x40000
plus the decoder class times 256 plus the index. This allocates hosted Lean
objects and is not a freestanding hardware-access boundary.

Tests first validate the retained capture hashes and selector list, then
synthetically clear Command while retaining Status. The model tests cover
missing, duplicated, reordered and malformed observations, wrong write shapes,
failed readback and changed bridge routing. The ABI tests give Lean and C the
same complete arrays and explicit expected results. These are synthetic trace
tests; no Qotom PCI write or hardware quiescence is claimed.

Remaining integration includes authoritative enumeration and initial-state
binding, a reviewed device and bridge policy, transaction quiescence, the
serial/recovery exceptions, whole-platform dispatch before q35-only MMIO,
and physical evidence. The existing q35 strategy is unchanged.
