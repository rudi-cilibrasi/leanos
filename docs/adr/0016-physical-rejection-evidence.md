# ADR 0016: Opt-in physical-machine rejection evidence

## Status

Accepted as an experimental, manually operated evidence tier.

## Decision

Add a separate `hardware` manifest and capture/verification command for the
first named Qotom J1900 observation. Its result class is `controlled-rejection`:
only the exact declared BOOT and `dma-identity` FINAL sequence passes. The
existing image intentionally admits q35, not this physical platform.

Keep this catalog separate from the required emulator matrix and experimental
KVM lane. Normal builds, PR checks, releases, and KVM preflight never initiate
a hardware capture. Offline validator tests and the compact captured observation
can be checked without hardware; a physical run remains opt-in and non-blocking.
No self-hosted runner, network endpoint, power controller, or firmware mutation
is introduced. See [the procedure](../qotom-hardware-bringup.md).

The profile binds one exact source revision, image/ELF/toolchain digests,
technical platform inventory, expected serial records, and bounded capture
settings. New artifacts or physical profiles require review of the first
reachable rejection and a manifest change. The runtime q35 admission policy
and all existing proof/security claims remain unchanged.

## Terminal and evidence contract

Serial FINAL is authoritative for the observation. The existing kernel still
writes QEMU debug-exit port `0xf4` and then executes its absorbing CLI/HLT loop;
physical evidence does not depend on the effect of that port write. A complete
180-second capture must contain the exact expected sequence and at least ten
seconds without bytes after its terminal record. Timeout alone, a different
rejection, user-entry/success, malformed output, and post-terminal bytes are
non-passing results. Firmware bytes preceding the first kernel marker are
retained but do not contribute to a kernel success claim.

A repository schema and independent verifier check all payload hashes, pinned
profile/source/artifacts, raw versus normalized bytes, timestamped event
reconstruction, operator-declared reset ordering, and classification. Recorded
result labels are not trusted. The reset marker is a human assertion; it is
not a hardware reset detector. Partial captures and infrastructure failures
retain diagnostics without becoming valid passing evidence bundles.

The first checked observation was acquired with a preceding version of the
capture script. Preserve its exact implementation, original raw/event bytes,
and original-result hash, identify it as imported, and recompute its result
under the integrated verifier. Do not claim it was collected by the later tool.

## Trust boundary and exclusions

This is finite integration evidence. It additionally trusts physical firmware,
SMM/SMI activity, CPU/chipset behavior, boot medium and BIOS disk services,
GRUB, UART/transceiver/null-modem wiring, observing host/USB adapter/drivers,
capture software and clocks, and operator selection/reset timing. It also
retains the existing trusted Lean/compiler/generated-C/assembly/linker boundary.
Neither hashes nor a transcript authenticate a potentially malicious operator.

The trace shows the expected pre-CPL3 rejection and no later records. Its
source-level placement precedes user entry; bounded serial silence supports
halt behavior but cannot independently prove CPU halt or absence of all
execution, DMA, AP, or SMM activity. It proves neither binary refinement nor
hardware admission, generic BIOS support, hardware VT-d operation, or safety
of executing later kernel stages on this machine. The source's first PCI
identity mismatch occurs before its first PCI Command write on this profile.

The machine's precise commercial case model and board revision are unavailable
in SMBIOS and remain explicitly unknown. The recorded CPU, AMI board/firmware,
full PCI identities, UART, and operator-confirmed physical setup bound this
observation. They do not qualify other products sharing a marketing name.

## Consequences

The physical trace and inventory provide a concrete input to a future typed
hardware-admission profile without weakening q35 today. Operators can reproduce
or diagnose the same bounded rejection. The procedure requires manual media
selection and recovery; a screen left showing GRUB can be misleading because
kernel output is serial-only. Resetting during capture can invalidate an
otherwise correct terminal sequence and must remain visible as a failure.

Raw capture data is preserved exactly. Publication may redact inventory-only
serials, UUIDs, and network identifiers while retaining technical platform
identity and documenting the omission. Never silently edit protocol bytes or
relabel timeout as a pass to obtain a distributable observation.
