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
