# PCI configuration read adapter

`boot/pci-config-read.h` provides a callback for `pci_enumerate_segment` that
includes the bus field. It rejects invalid device/function indices, unaligned
offsets and a null destination before performing I/O or changing the output.
The interface covers segment zero and conventional 256-byte configuration
space only. It does not truncate an invalid offset into a different register.

`boot/pci-config-read.S` performs a privileged x86-64 mechanism-1 dword read.
It saves flags, disables ordinary interrupts, writes the selected address to
CF8, reads CFC, restores flags and returns the raw dword. CF8 retains the
selected address. No device configuration data is written. This requires
mechanism-1 hardware support and exclusive access from the BSP; it does not
exclude NMI, SMM or another CPU. All such agents must independently refrain
from CF8/CFC access. An I/O fault follows the caller's terminal exception
policy and does not return an adapter failure or promise flags restoration.
All-ones data remains an observation, not proof of device absence or successful
hardware access. The collector uses its existing vendor-FFFF absence contract.

The caller must own writable output storage, including across any interrupt
after flags restoration. This component does not establish snapshot atomicity,
DMA containment, firmware trust or admission. It is not wired into the boot
path yet. Production q35 helpers remain unchanged; boot capture and its
offline inventory replay are the next integration boundary for issue #330.

`scripts/check-pci-config-read.py` tests all 4,194,304 legal address tuples
against an arithmetic oracle, rejects invalid arguments without a transport
call or output write, and feeds a synthetic function at 255:31.7 through the
actual complete-segment collector. A native-object instruction audit requires
the exact save/CLI/address-write/data-read/restore/return sequence and rejects
nine mutations. Hosted tests substitute the I/O leaf; they do not execute
privileged I/O, establish hardware behavior or prove the external exclusion
assumptions. Run with pinned GCC and Clang using `LEANOS_CC`.

`scripts/test-pci-config-read-qemu.py` executes the actual assembly leaf and
callback in an isolated freestanding QEMU fixture. The fixture masks both
PICs, runs one CPU and identity-maps its RAM. It captures flags immediately
after native reads with IF clear and set, checking both the host identity
and exact seeded flags (`0x47` and `0x247`). It then runs the actual complete
segment collector and emits all sixteen dwords of each header to debugcon.
The guest halts after a completion marker while the runner queries QMP.

Two topologies cover the root bus alone and endpoints behind two bridges.
The runner compares the complete, strictly ordered set of BDFs, vendor/device
identities and class/subclass values with QMP's independently reported device
inventory. The bridged case must contain two distinct nonzero buses. QMP does
not independently validate the remaining header dwords. Four executed
mutations must fail validation: bus forced to zero, reading the address port
instead of the data port, discarding saved flags and unconditionally enabling
interrupts. A guest timeout or crash fails the test, including negative cases;
it cannot substitute for the expected completed capture and rejection.

Run `LEANOS_CC=gcc python3 scripts/test-pci-config-read-qemu.py` and repeat
with `LEANOS_CC=clang-18` in the pinned CI image. Per-compiler artifacts under
`build/pci-config-read/qemu-*` include the ELF, native object, QEMU command,
raw guest output, QMP inventory, compiler/QEMU versions and object/ELF hashes.
The ordinary check script includes this test. These emulator observations do
not establish physical Qotom behavior, interrupt interleaving correctness,
NMI/SMM exclusion, bus-master quarantine or production platform admission.
