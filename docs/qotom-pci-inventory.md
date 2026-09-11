# Qotom PCI inventory candidate

`LeanOS.QotomPCIInventory` compares a bounded, ordered list of decoded PCI
headers with the complete 15-function inventory captured on 2026-09-10 in
`hardware/lab/observations/qotom-pci-20260910/`. This candidate names the AHCI
controller 8086:0f23/class 010601. It does not accept the older IDE observation
8086:0f21/class 01018a or select a production boot profile.

The comparison binds each function's BDF, vendor/device/class identity,
multifunction bit, and endpoint/bridge layout. For each of the four bridges,
it also binds primary, secondary, subordinate, and bridge-control registers.
Every function must occur once in the captured canonical order. Missing or
extra functions fail the count check; relocation, duplication, reordering,
identity, multifunction, routing, and malformed-header failures carry typed
errors, with an index where applicable.

A successful witness retains the complete decoded headers and their original
16 dwords. Its proof binds the entire projected inventory to one baseline;
another theorem establishes its 15-function length. The general
`check_preserves_raw` theorem proves that any successful check returns exactly
the supplied raw headers in their original order, including every command and
window register. Command/status, revision,
BARs, and forwarding-window contents are observations for later policy. They
are not frozen to values supplied by a running FreeBSD instance.

This module assumes the caller supplies a complete enumeration. It does not
prove enumeration completeness, stop DMA, validate forwarding windows, check
command readback, select an IOMMU strategy, permit CPL3, or access hardware.
The kernel does not yet call it. Its success must not substitute for the
quarantine boundary required by issue #330.

Run `lake build LeanOS.QotomPCIInventory`, then
`python3 scripts/test-qotom-pci-inventory.py`. The replay first validates the
retained capture's raw digests and selector inventory through the existing
header replay. It checks the complete capture, every function's identity and
address mutations, bridge routing/control mutations, malformed headers,
missing/extra/reordered functions, and IDE/q35 mixtures. A positive mutation
also confirms that command/window values remain available to later checks.
The `leanos_qotom_pci_inventory_check` export consumes an `Array UInt64`
containing exactly 285 words: fifteen slots of bus, device, function, and sixteen
configuration dwords. A separate declared count must equal fifteen. Count
failure is 0x10000, array-size failure is 0x10001, and success is 1. Typed
header errors use 0x20000 plus decoder reason offset times 256 plus function
index; address, identity, multifunction, and routing use bases 0x30000,
0x40000, 0x50000, and 0x60000 plus index respectively. This allocation-using
hosted interface is not yet a freestanding machine adapter.

`python3 scripts/test-qotom-pci-abi.py` emits complete snapshots with explicit
expected results for Lean and `tests/qotom-pci-inventory-host.c`. Ordinary
Lean/generated-C parity passes 94 cases. The shared hosted harness runs these same 94 cases in ordinary and pinned
ASan/UBSan modes, with generated export declarations and execution coverage;
both modes pass. Run `./scripts/check-qotom-pci-inventory-host.sh ordinary`,
then `./scripts/check-qotom-pci-inventory-host.sh sanitized` in the pinned CI
container. Production integration remains pending.

The hosted executable also accepts `inventory COUNT WORD...` for offline
replay of external observations. Supply nineteen words per function: bus,
device, function, then the sixteen raw configuration dwords. The transport
accepts at most sixteen functions, requires exactly the declared number of
words, and parses canonical unsigned decimal values through `UINT64_MAX`.
It rejects signs, whitespace, leading zeroes, overflow and trailing text
before allocating the input array. The generated decoder remains responsible
for BDF and dword widths and the complete candidate inventory policy.

For example, `build/qotom-pci-inventory-host/host inventory 0` prints `65536`
and exits zero: parsing succeeded, but the model rejected the empty inventory.
A matching complete observation prints `1`. Malformed arguments exit with
status two and no result on stdout. The fixed ABI corpus runs before external
replay; invoking the executable without arguments retains the original test
mode. `scripts/test-qotom-pci-replay-cli.py --replay EXECUTABLE` checks the
hash-verified retained capture, model rejection and malformed CLI inputs, and
is included in both ordinary and sanitized hosted checks. This input interface
does not establish the provenance or completeness of an external observation.
