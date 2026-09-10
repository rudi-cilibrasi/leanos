# Bounded PCI enumeration component

`boot/pci-enumeration.h` collects the first sixteen configuration dwords of
every readable function in one configuration segment. It scans all 256 buses,
32 devices and eight functions in ascending order. It does not skip functions
based on function zero, multifunction flags, or a supplied allowlist. This
provides the bounded collection component needed before the Qotom inventory
checker can compare a complete observation with its reviewed baseline.

The read callback supplies each aligned dword and reports access failure.
An all-ones vendor is treated as absence, matching the existing q35 observation
assumption. At most sixteen headers fit in the caller-owned snapshot. A read
failure or seventeenth present function returns a typed error with its exact
BDF and offset. The published count stays zero on every failure; header storage
may contain partial data and must not be consumed. Success publishes the count
only after the entire segment has been scanned. No allocator or write callback
is used. There are at most 65,776 reads on success and no retries; the callback
must itself terminate for that bound to imply termination.

Successful enumeration does not mean platform admission. An empty segment,
missing baseline function, changed identity or extra readable function remains
an observation for the existing inventory checker to reject. The collector
does not certify configuration access, snapshot atomicity, other segments,
devices hidden by firmware or hardware, bridge forwarding, DMA quiescence, or
device behavior. The caller must serialize configuration access and establish
the meaning and completeness of hardware observations. No physical configuration
access or quarantine is performed by the hosted tests.

`scripts/check-pci-enumeration.sh` verifies the retained capture hashes before
building its C fixture. It checks every address and read offset, exact raw
header preservation, missing and rogue functions, an isolated function at the
last possible address, empty inventory, capacity overflow, and failures at
every captured header word plus the last absent slot. Its `sanitizers` mode
uses the repository's pinned ASan/UBSan configuration. The collector is also
compiled as a separate freestanding object and checked for runtime dependencies.

The component is not wired into the boot path. Remaining work for issue #330
includes the actual serialized hardware-access adapter, binding its output to
generated admission, reviewed device and bridge policy, ordered writes and
readback, transaction quiescence, serial/recovery exceptions, whole-platform
dispatch, and physical evidence. Production q35 behavior remains unchanged.
