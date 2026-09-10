# Read-only FreeBSD PCI header capture

`capture-pci.py OUTPUT` runs on FreeBSD with Python 3 and sufficient privilege
to read `/dev/pci`. For example, `sudo python3 capture-pci.py /tmp/pci-capture`.
The output directory must be new. The collector lists OS-enumerated functions,
reads the first 64 configuration bytes of each, and lists again to detect an
inventory change. It retains raw text and SHA-256 hashes before decoding;
`inventory.json` exists only after the complete collection succeeds.

The collector uses only `pciconf -l` and `pciconf -r SELECTOR 0x0:0x3c`, whose
read semantics are documented in the [FreeBSD pciconf manual](https://man.freebsd.org/cgi/man.cgi?query=pciconf&sektion=8).
It performs no configuration writes, device attachment, BAR sizing or BAR
MMIO reads. All functions returned by FreeBSD are collected, bounded at 64;
it does not restrict observations to an expected allowlist. Raw multifunction
bits and bridge bus/control fields are decoded from the headers.

A Linux caller can import `collect(output_path, run)` and supply an SSH command
adapter when Python is unavailable on FreeBSD. The adapter must execute the
argument vectors on the intended target, propagate failures, and return ASCII
stdout. Keep separate provenance naming the target, transport, collector source
hash and any unreliable target clock. The report's `collector_system` and
`collector_release` describe the Python process, not necessarily the PCI host.

Run `python3 scripts/test-pci-capture.py` for fake-command tests; these access
no hardware. See `observations/qotom-pci-20260910` for the first physical capture.

This is evidence collection, not admission. Live drivers can change registers
between reads, and an unchanged listing does not make the headers atomic.
FreeBSD enumeration does not prove that a future LeanOS scan finds every
function, nor does an enabled/disabled command bit establish DMA containment.
IOMMU capability and device-specific quiescence need separate evidence.
